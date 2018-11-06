{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module TestTH where

import           Language.Haskell.TH

{-# ANN module "HLint: ignore" #-}

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

newtype PubKey = PubKey { getPubKey :: Int }
type Height = Int
type Value = Int
newtype Signed a = Signed (PubKey, a)
newtype OracleValue a = OracleValue (Signed (Height, a))

data MyData = 
    NoData
    | SomeData (OracleValue Value)

getVal :: Q Exp
getVal = [|  
        \(m :: MyData) ->
            case m of
                NoData -> 100
                SomeData ov ->
                    case ov of
                        OracleValue (Signed (_, (_, a))) -> a  
        |]