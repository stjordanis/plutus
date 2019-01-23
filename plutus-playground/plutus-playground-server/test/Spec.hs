module Main
    ( main
    ) where

import qualified Playground.APISpec      as API
import qualified Playground.UsecasesSpec as Usecases
import           Test.Hspec              (hspec)

main :: IO ()
main =
    hspec $ do
        API.spec
        Usecases.spec
