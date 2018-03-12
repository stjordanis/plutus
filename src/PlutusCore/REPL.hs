{-# OPTIONS -Wall #-}





module PlutusCore.REPL where

import PlutusCore.REPLTools

import System.Environment





main :: IO ()
main =
  do locs <- getArgs
     replFiles locs