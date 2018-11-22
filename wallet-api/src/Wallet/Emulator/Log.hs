{-# LANGUAGE DeriveGeneric #-}
module Wallet.Emulator.Log(
    EmulatorEvent,
    EmEvent(..)
    ) where

import           Data.Aeson        (FromJSON, ToJSON)
import           GHC.Generics      (Generic)

import qualified Wallet.UTXO.Index as UTXO
import qualified Wallet.UTXO.Types as UTXO

type EmulatorEvent = EmEvent UTXO.TxId'

-- | Events produced by the mockchain
data EmEvent a =
    TxnSubmit a
    -- ^ A transaction has been added to the global pool of pending transactions
    | TxnValidate a
    -- ^ A transaction has been validated and added to the blockchain
    | TxnValidationFail a UTXO.ValidationError
    -- ^ A transaction failed  to validate
    | BlockAdd [a]
    -- ^ A block has been added to the blockchain
    deriving (Eq, Ord, Show, Generic, Functor)

instance FromJSON a => FromJSON (EmEvent a)
instance ToJSON a => ToJSON (EmEvent a)
