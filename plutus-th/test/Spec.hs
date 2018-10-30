{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ViewPatterns        #-}
-- remove when we can use addCorePlugin
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}

-- | Most tests for this functionality are in the plugin package, this is mainly just checking that the wiring machinery
-- works.
module Main (main) where

import           Common
import           Data.Maybe                               (isJust)

import           TestTH

import           Language.Plutus.TH

import           Language.Plutus.CoreToPLC.Plugin         (getAst, lifted)
import           Language.PlutusCore                      (applyProgram)
import           Language.PlutusCore.Evaluation.CkMachine (runCk)
import           Language.PlutusCore.Evaluation.Result    (evaluationResultToMaybe)
import qualified Language.PlutusCore.Pretty               as PLC

import           Test.Tasty
import           Test.Tasty.HUnit

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

golden :: String -> PlcCode -> TestNested
golden name = nestedGoldenVsDoc name . PLC.prettyPlcClassicDebug . getAst

tests :: TestNested
tests = testGroup "plutus-th" <$> sequence [
    golden "simple" simple
    , golden "power" powerPlc
    , golden "and" andPlc
    , pure $ testGroup "LiftPlc" [
          testCase "Should check signatures in lifted value" (testCount (lifted [Signature 1]) @?= True)
        , testCase "Should check signatures in TH value" (testCount sigs' @?= True)
    ]
  ]

simple :: PlcCode
simple = $(plutus [| \(x::Bool) -> if x then (1::Int) else (2::Int) |])

-- similar to the power example for Feldspar - should be completely unrolled at compile time
powerPlc :: PlcCode
powerPlc = $(plutus [| $(power (4::Int)) |])

andPlc :: PlcCode
andPlc = $(plutus [| $(andTH) True False |])

sigs' :: PlcCode
sigs' = $(plutus [| $(sigs) |])

testCount :: PlcCode -> Bool
testCount (getAst -> inp) = isOk where
    isOk = isJust $ evaluationResultToMaybe $ runCk prog
    prog = count `applyProgram` inp
    count = getAst $(plutus [| $(TestTH.checkTxInSigs) |])
