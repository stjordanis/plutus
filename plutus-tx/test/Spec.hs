{-# LANGUAGE ScopedTypeVariables #-}
module Main
    ( main
    ) where

import qualified Lift.Spec         as Lift
import qualified Plugin.Spec       as Plugin
import qualified TH.Spec           as TH

import           Common

import qualified Bazel.Runfiles    as Runfiles
import qualified Control.Exception as E

import           Test.Tasty

main :: IO ()
main = do
    mr <-
        E.catch
            (Just <$> Runfiles.create)
            (\(e :: E.SomeException) -> pure Nothing)
    let testDir =
            case mr of
                Just r  -> Runfiles.rlocation r "plutus/plutus-tx/"
                Nothing -> "."
    defaultMain $ runTestNestedIn [testDir, "test"] tests

tests :: TestNested
tests = testGroup "tests" <$> sequence [Plugin.tests, Lift.tests, TH.tests]
