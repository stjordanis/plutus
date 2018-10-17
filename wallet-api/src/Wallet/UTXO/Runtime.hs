{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards  #-}
-- | A model of the types involved in transactions. These types are intented to
--   be used in PLC scripts.
module Wallet.UTXO.Runtime (-- * Transactions and related types
                PubKey(..)
              , Value
              , Height
              , PendingTxOutRef(..)
              , TxId
              , Hash
              , Signature(..)
              -- * Pending transactions
              , PendingTx(..)
              , PendingTxOut(..)
              , PendingTxIn(..)
              , PendingTxOutType(..)
              , mkPending
              -- * Oracles
              , Signed(..)
              , OracleValue(..)
              ) where

import           Data.Bits            ((.|.))
import qualified Data.Bits            as Bits
import qualified Data.ByteArray       as BA
import           Data.Foldable        (foldl')
import           Data.List            (inits, tails)
import           Data.Memory.Endian   (LE (..), fromLE)
import qualified Data.Set             as Set
import           Data.Word            (Word32)
import           GHC.Generics         (Generic)
import           Language.Plutus.Lift (LiftPlc (..), TypeablePlc (..))
import           Language.Plutus.TH   (PlcCode)
import           Wallet.API           (PubKey (..))
import           Wallet.UTXO          (Signature (..), TxId, UtxoLookup)
import qualified Wallet.UTXO          as UTXO

data PendingTxOutType =
    PubKeyTxOut PubKey -- ^ Pub key address
    | DataTxOut -- ^ The data script of the pending transaction output (see note [Script types in pending transactions])
    deriving Generic

instance TypeablePlc PendingTxOutType
instance LiftPlc PendingTxOutType

-- | Output of a pending transaction.
data PendingTxOut d = PendingTxOut {
    pendingTxOutValue   :: Value,
    pendingTxDataScript :: Maybe d, -- ^ Note: It would be better if the `DataTxOut` constructor of `PendingTxOutType` contained the `d` value (because the data script is always `Nothing` for a pub key output). However, this causes the core-to-plc converter to fail with a type error on a pattern match on `PubKeyTxOut`.
    pendingTxOutData    :: PendingTxOutType
    } deriving Generic

instance TypeablePlc d => TypeablePlc (PendingTxOut d)
instance (TypeablePlc d, LiftPlc d) => LiftPlc (PendingTxOut d)

data PendingTxOutRef = PendingTxOutRef {
    pendingTxOutRefId  :: Hash,
    pendingTxOutRefIdx :: Int,
    pendingTxOutSigs   :: [Signature]
    } deriving Generic

instance TypeablePlc PendingTxOutRef
instance LiftPlc PendingTxOutRef

-- | Input of a pending transaction.
data PendingTxIn r = PendingTxIn {
    pendingTxInRef         :: PendingTxOutRef,
    pendingTxInRefRedeemer :: Maybe r -- ^ The redeemer of the pending transaction input (see note [Script types in pending transactions])
    } deriving Generic

instance TypeablePlc r => TypeablePlc (PendingTxIn r)
instance (TypeablePlc r, LiftPlc r) => LiftPlc (PendingTxIn r)

-- | A pending transaction as seen by validator scripts.
data PendingTx r d = PendingTx {
    pendingTxCurrentInput :: (PendingTxIn r, Value), -- ^ The input we are validating
    pendingTxOtherInputs  :: [(PendingTxIn r, Value)], -- ^ Other transaction inputs (they will be validated separately but we can look at their redeemer data and coin value)
    pendingTxOutputs      :: [PendingTxOut d],
    pendingTxForge        :: Value,
    pendingTxFee          :: Value,
    pendingTxBlockHeight  :: Height,
    pendingTxSignatures   :: [Signature]
    } deriving Generic

instance (TypeablePlc r, TypeablePlc d) => TypeablePlc (PendingTx r d)
instance (TypeablePlc r, TypeablePlc d, LiftPlc r, LiftPlc d) => LiftPlc (PendingTx r d)

-- `OracleValue a` is the value observed at a time signed by
-- an oracle.
newtype OracleValue a = OracleValue (Signed (Height, a))
    deriving Generic

instance TypeablePlc a => TypeablePlc (OracleValue a)
instance (TypeablePlc a, LiftPlc a) => LiftPlc (OracleValue a)

newtype Signed a = Signed (PubKey, a)
    deriving Generic

instance TypeablePlc a => TypeablePlc (Signed a)
instance (TypeablePlc a, LiftPlc a) => LiftPlc (Signed a)

-- | Ada value
--
-- TODO: Use [[Wallet.UTXO.Types.Value]] when Integer is supported
type Value = Int

type Hash = Int

-- | Blockchain height
--   TODO: Use [[Wallet.UTXO.Height]] when Integer is supported
type Height = Int

-- | Turn a UTXO transaction with @n@ inputs into a list of @n@ pending
--   transactions. Each pending transaction has a different
--   `pendingTxCurrentIn`, and is paired with its validator script (if it
--   happens to be a scripted transaction input).
mkPending :: (Applicative m, UtxoLookup m)
    => UTXO.Height -- ^ Height of the blockchain
    -> UTXO.Tx -- ^ Transaction currently being validated
    -> m [(Maybe PlcCode, PendingTx PlcCode PlcCode)]
mkPending h UTXO.Tx{..} =
    fmap (uncurry rump) <$> fmap rotate (traverse prepareInput inputs) where
        inputs  = Set.toList txInputs

        -- The pending transactions share most of their fields, the only
        -- difference is in `pendingTxCurrentInput` and `pendingTxOtherInputs`.
        rump (validator, cur) rst = (validator, PendingTx{..}) where
            pendingTxCurrentInput = cur
            pendingTxOtherInputs = rst
            pendingTxOutputs = mkOut <$> txOutputs
            pendingTxForge = fromIntegral txForge
            pendingTxFee = fromIntegral txFee
            pendingTxBlockHeight = fromIntegral h
            pendingTxSignatures = txSignatures

        mkOut (UTXO.TxOut _ v t') = PendingTxOut v' d s where
            v' = fromIntegral v
            (d, s) = case t' of
                UTXO.PayToPubKey k                   -> (Nothing, PubKeyTxOut k)
                UTXO.PayToScript (UTXO.DataScript c) -> (Just c, DataTxOut)

-- | Given a transaction input of type `UTXO.TxIn'`, get all the data we need
--   to run the validation script of this input. Since `UTXO.TxIn'` only
--   contains a *reference* (by hash) to the original transaction, we need to
--   find the transaction first. This is enabled by the `UtxoLookup`
--   constraint.
--
--   Then we can assemble the input, which includes
--
--   * The validator script itself (first part of the tuple). `Nothing` means
--     it is a pay-to-pubkey output.
--   * A `PendingTxIn PlcCode`, which includes the data script from the
--     original transaction.
--   * The value of the transaction output that is consumed by the `UTXOTxIn'`.
--
--  The latter two are intended to be converted to PLC using `LiftPLC`.
--
prepareInput :: (Applicative m, UtxoLookup m)
    => UTXO.TxIn'
    -> m (Maybe PlcCode, (PendingTxIn PlcCode, Value))
prepareInput i = fmap assocr ((,) <$> mkIn i <*> valueOf i) where
    mkIn (UTXO.TxIn ref tp) = flip fmap (mkOutRef ref) $ \ref' ->
        case tp of
            UTXO.ConsumeScriptAddress (UTXO.Validator v) (UTXO.Redeemer r) ->
                (Just v, PendingTxIn ref' (Just r))
            UTXO.ConsumePublicKeyAddress _                                 ->
                (Nothing, PendingTxIn ref' Nothing)
    mkOutRef t@(UTXO.TxOutRef h' idx) =
        PendingTxOutRef (mkHash h') idx <$> UTXO.lkpSigs t

-- | Given a list `l` of '(a,b)'s, `rotate l` pairs each `(a, b)` with the list
--   of all other `b`s.
--
-- >>> rotate [("a", 1), ("b", 2), ("c", 3)]
-- >>> [(("b",2),[3,1]),(("c",3),[1,2]),(("a",1),[2,3])]
-- >>> rotate []
-- >>> []
--
rotate :: [(a, b)] -> [((a, b), [b])]
rotate t' = drop 1
    $ (\(l, r) -> let lst = r ++ l in (head lst, snd <$> drop 1 lst))
    <$> zip (inits t') (tails t')

assocr :: ((a, b), c) -> (a, (b, c))
assocr ((a, b), c) = (a, (b, c))

-- | The PLC representation of a `UTXO.TxId'`.
--
--   To get an [[Int]] from the [[Digest SHA256]] we simply take the first four
--   bytes of the hash.
mkHash :: UTXO.TxId' -> Hash
mkHash (UTXO.TxId h) = fromIntegral $ fromLE (LE w) where
    w = foldl' (.|.) 0 bs'
    bytes = BA.unpack $ BA.takeView h 4
    bs' = fmap shiftWord (zip (fromIntegral <$> bytes) [0,8..])

    shiftWord (b :: Word32, s) = Bits.shiftL b s

valueOf :: UtxoLookup m => UTXO.TxIn' -> m Value
valueOf = fmap fromIntegral . UTXO.lkpValue . UTXO.txInRef
