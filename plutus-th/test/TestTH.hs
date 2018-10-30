{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
module TestTH where

import           GHC.Generics         (Generic)
import           Language.Haskell.TH
import           Language.Plutus.Lift (LiftPlc (..), TypeablePlc (..))
{-# ANN module "HLint: ignore" #-}

newtype Signature = Signature { getSignature :: Int }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    -- NOTE: Commenting out the following line,
    --       and uncommenting the one after that
    --       will make the error go away!
    deriving newtype (LiftPlc)
-- instance LiftPlc Signature
instance TypeablePlc Signature

power :: Int -> Q Exp
power n =
    if n <= 0 then
        [| \ _ -> (1::Int) |]
    else if even n then
        [| \(x::Int) -> let y = $(power (n `div` (2::Int))) x in y * y |]
    else
        [| \(x::Int) -> x * ($(power (n - (1::Int))) x) |]

andTH :: Q Exp
andTH = [|\(a :: Bool) -> \(b::Bool) -> if a then if b then True else False else False|]


checkTxInSigs :: Q Exp
checkTxInSigs =  [|

    -- Check if all signature correspond to the key `10`
    \(inp :: [Signature]) ->
        let

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) l r = if l then r else False

            checkSigs :: [Signature] -> Bool
            checkSigs l =
                case l of
                    (x::Signature):(xs::[Signature]) ->
                        case x of
                            Signature i -> i == 10 && checkSigs xs
                    ([]::[Signature]) -> True

        in
            checkSigs inp
    |]

sigs :: Q Exp
sigs = [| Signature 5 : ([]::[Signature]) |]
