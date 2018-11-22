{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}
module Wallet.Emulator.TypesNew where

import           Control.Lens
import           Control.Monad         ((>=>))
import           Control.Monad.Reader  (MonadReader (..))
import           Control.Monad.Writer  (MonadWriter (..))
import           Data.Map              (Map)
import           Data.Maybe            (catMaybes)
import           Data.Semigroup
import qualified Data.Set              as Set
import qualified Data.Text             as Text

import qualified Wallet.API            as API
import           Wallet.Emulator.Types (Wallet, WalletState)
import           Wallet.UTXO           (Height, Tx, TxOutRef')
import           Wallet.UTXO.Index     (UtxoIndex, deleteOutRefs, outRefs)
import qualified Wallet.UTXO.Index     as Index

-- This is a proposal for splitting up the `EmulatorState` type and related
-- functions in Wallet.Emulator.Types.
-- There are two main changes.
-- 1. The actions that modify the state produce events, which can be one of
--    three types (ChainEvent, EmulatorEvent, WalletEvent)
-- 2. The state of the global mockchain is represented by a `ChainState` type,
--    with a nice semigroup instance.
-- As a result we will be able to replace a lot the functions in
-- Wallet.Emulator.Types with ones that have more precise constraints, and we
-- can get a list of `MockchainEvent TxId'` to give back to the user at the end.

-- | Events that happen on the blockchain (global state)
data ChainEvent a =
    BlockAdded Height [a]
    | TxValidated a
    | TxValidationFailed a Index.ValidationError
    deriving Functor

makeClassyPrisms ''ChainEvent

-- | Events covering the interface between wallets and the chain
data EmulatorEvent a =
    TxnSubmitted a
    | WalletNotified Wallet Height
    deriving Functor

makeClassyPrisms ''EmulatorEvent

-- | Events that are specific to a wallet
data WalletEvent =
    WalletLog Text.Text
    | TriggerFired API.EventTrigger

makeClassyPrisms ''WalletEvent

data MockchainEvent h =
    ChainEventE (ChainEvent h)
    | EmulatorEventE (EmulatorEvent h)
    | WalletEventE Wallet WalletEvent
    deriving Functor

makeClassyPrisms ''MockchainEvent

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

fromTx :: Tx -> ChainState
fromTx = undefined

fromBlock :: [Tx] -> ChainState
fromBlock = set blocks 1 . foldMap fromTx

validateTx :: (
    AsChainEvent Tx e,
    MonadReader ChainState m,
    MonadWriter [e] m)
    => Tx
    -> m (Maybe Tx)
validateTx = undefined
    -- TODO: Use Index to validate the txn

-- | Validate a block of transactions and append it to the
--   [[ChainState]], emitting log messages in the process
validateBlock :: (
    AsChainEvent Tx e,
    MonadReader ChainState m,
    MonadWriter [e] m,
    MonadWriter ChainState m)
    => [Tx]
    -> m ()
validateBlock =
    traverse validateTx >=> tell . fromBlock . catMaybes

data EmulatorState = EmulatorState {
    _chain     :: ChainState,
    _pendingTx :: [Tx],
    _wallets   :: Map Wallet WalletState
    }

makeLenses ''EmulatorState
