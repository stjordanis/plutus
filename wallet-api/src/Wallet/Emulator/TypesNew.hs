{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
module Wallet.Emulator.TypesNew where

import           Control.Lens
import           Control.Monad.Reader  (MonadReader (..))
import           Control.Monad.State   (MonadState (..))
import           Control.Monad.Writer  (MonadWriter (..))
import           Data.Map              (Map)
import           Data.Maybe            (catMaybes)
import           Data.Semigroup
import qualified Data.Set              as Set
import qualified Data.Text             as Text

import qualified Wallet.API            as API
import           Wallet.Emulator.Types (Wallet, WalletState, EmulatedWalletApi)
import           Wallet.UTXO           (Height, Tx, TxOutRef')
import           Wallet.UTXO.Index     (UtxoIndex, deleteOutRefs, outRefs)
import qualified Wallet.UTXO.Index     as Index

-- This is a proposal for splitting up the `EmulatorState` type and related
-- functions in Wallet.Emulator.Types.
--
-- The underlying idea is that the emulator state is a made up of two 
-- parts: A collection of wallets, each with their own `WalletState`,
-- and a blockchain. The state of each part can be changed by events, and
-- the parts interact by producing events that can be consumed on the other side
-- Diagram:
--
--    /-----------> Submit transactions   -->\
-- Wallets                              Blockchain
--   \<------------ Notify of new blocks <---/
--
-- This is reflected in the signatures of `processMockchain` (which consumes a 
-- `ChainEvent` and produces `WalletEvent`s) and `processWallet` (which 
-- consumes a `WalletEvent` and produces `ChainEvent`s).
-- 
-- processWallet :: (
--     AsEmulatorLog e Tx,
--     AsChainEvent e Tx,
--     MonadWriter [e] m,
--     MonadState WalletState m)
--     => WalletEvent EmulatedWalletApi Tx
--     -> m ()
-- 
-- processMockchain :: (
--     MonadState EmulatorState m,
--     AsEmulatorLog e Tx,
--     AsWalletEvent e n Tx,
--     MonadReader ChainState m,
--     MonadWriter [e] m)
--     => ChainEvent Tx
--     -> m ()
--
-- `EmulatorLog` is a third type of event that doesn't directly map to a state 
-- change in either of the two parts. It conveys information that can be used
-- for debugging purposes.


data EmulatorLog a =
    TxValidated a
    | TxValidationFailed a Index.ValidationError
    | WalletLog Text.Text
    | TriggerFired API.EventTrigger
    deriving Functor
makeClassyPrisms ''EmulatorLog

-- | Events that change the state of the blockchain (global state)
data ChainEvent a =
    SubmitTx a
    -- ^ A new transaction is submitted to the pool of pending transactions
    | ProcessPending
    -- ^ Pending transactions are processed, resulting in a new block
    deriving Functor
makeClassyPrisms ''ChainEvent

-- | Events that change the state of a wallet
data WalletEvent n a = 
    NotifyBlock [a]
    | WalletAction (n ())
    deriving Functor

makeClassyPrisms ''WalletEvent

data MockchainLog n h =
    ChainEventE (ChainEvent h)
    | EmulatorLogE (EmulatorLog h)
    | WalletEventE Wallet (WalletEvent n h)
    deriving Functor

makeClassyPrisms ''MockchainLog

-- | A pair of consumed and produced transaction outputs (the latter
--   represented by a [[UtxoIndex]], covering a range of blocks.
--
--   [[ChainState]] contains all the information needed to validate a
--   transaction, provided its inputs were all produced within the last
--   `chainStateBlocks` blocks.
data ChainState = ChainState {
        _consumed :: Set.Set TxOutRef',
        _produced :: UtxoIndex,
        _blocks   :: Sum Height
        -- ^ Amount of blocks covered by this `ChainState`. Note:
        --   Could also be a range `(Min Height, Max Height)`, which would
        --   allow us to see if we go back all the way to the beginning
        --   of the chain, BUT wouldn't have a monoid instance.
        --   (We can also check if the `consumed` set is empty, in which
        --   case it is likely that we go all the way back)
    } deriving (Eq, Ord, Show)

makeLenses ''ChainState

instance Semigroup ChainState where
    ChainState lc lp lh <> ChainState rc cp rh = ChainState c' p' h' where
        deltaL = lp `deleteOutRefs` rc
        deltaR = rc Set.\\ outRefs lp
        c' = lc <> deltaR
        p' = cp <> deltaL
        h' = lh <> rh

instance Monoid ChainState where
    mappend = (<>)
    mempty = ChainState mempty Index.empty mempty

-- | A list of transactions that have been submitted to the chain
--   and are yet to be validated
newtype TxPool = TxPool [Tx]
    deriving (Eq, Ord, Show, Semigroup)

makePrisms ''TxPool

type Mockchain = (TxPool, ChainState)

fromTx :: Tx -> ChainState
fromTx = undefined

fromBlock :: [Tx] -> ChainState
fromBlock = set blocks 1 . foldMap fromTx

validateTx :: (
    AsEmulatorLog e Tx,
    MonadReader ChainState m,
    MonadWriter [e] m)
    => Tx
    -> m (Maybe Tx)
validateTx txn = do
    Sum height <- view blocks
    idx <- view produced
    case Index.runValidation (Index.validateTransaction height txn) idx of
        Left e -> do
            tell [review _TxValidationFailed (txn, e)]
            pure Nothing
        Right () -> do
            tell [review _TxValidated txn]
            pure (Just txn)

-- | Validate a block of transactions, emitting log messages in the process
validateBlock :: (
    AsEmulatorLog e Tx,
    MonadReader ChainState m,
    MonadWriter [e] m)
    => [Tx]
    -> m [Tx]
validateBlock =
    fmap catMaybes . traverse validateTx 

data EmulatorState = EmulatorState {
    _mockchain :: Mockchain,
    _wallets   :: Map Wallet WalletState
    }

makeLenses ''EmulatorState

processMockchain :: (
    MonadState EmulatorState m,
    AsEmulatorLog e Tx,
    AsWalletEvent e n Tx,
    MonadReader ChainState m,
    MonadWriter [e] m)
    => ChainEvent Tx
    -> m ()
processMockchain = \case
    SubmitTx a ->
        modifying (mockchain . _1 . _TxPool) (a :)
    ProcessPending -> do
        txPool <- use (mockchain . _1 . _TxPool)
        newBlock <- validateBlock txPool
        mockchain . _2 <>= fromBlock newBlock
        mockchain . _1 . _TxPool .= []
        tell [review _NotifyBlock newBlock]

processWallet :: (
    AsEmulatorLog e Tx,
    AsChainEvent e Tx,
    MonadWriter [e] m,
    MonadState WalletState m)
    => WalletEvent EmulatedWalletApi Tx
    -> m ()
processWallet = \case
    NotifyBlock blck -> undefined

