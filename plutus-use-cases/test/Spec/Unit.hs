{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- | Some unit tests for validator scripts 
module Spec.Unit where

import           GHC.Generics         (Generic)
import           Language.Haskell.TH
import           Language.Plutus.Lift
import           Wallet.UTXO.Runtime

import           Prelude              (Bool (..), Eq (..), Int, Maybe (..), Num (..), Ord (..), div, even, ($))

{-# ANN module "HLint: ignore" #-}

myTxn :: PendingTx
myTxn = PendingTx
    { pendingTxInputs      = []
    , pendingTxOutputs     = []
    , pendingTxForge       = 0
    , pendingTxFee         = 0
    , pendingTxBlockHeight = 10
    , pendingTxSignatures  = []
    }

work :: Q Exp
work = [|
    let
        f :: PendingTx -> Bool
        f d =
            let
                PendingTx _ _ _ _ _ sigs = d

                isSigned :: Signature -> Bool
                isSigned (Signature i) = i == 10

                go :: [Signature] -> Bool
                go _ = False
                -- go l = case l of
                --             (s :: Signature):(r::[Signature]) -> if isSigned s then True else go r
                --             ([]::[Signature])                 -> False

            in go sigs

    in f |]
