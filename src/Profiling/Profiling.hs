module Profiling.Profiling where

import PlutusCore.Evaluation
import PlutusCore.Term
import Utils.ABT
import Utils.Pretty
import Utils.Vars


main :: IO ()
main = do
  putStrLn $ unwords (map pretty isas)
  putStrLn $ unwords (map pretty insts)
  putStrLn $ unwords (map pretty apps)
  putStrLn $ unwords (map pretty adds)
  
  where
    numCopies = 10000000
    
    isas :: [Term]
    isas = map ($ ()) $ replicate numCopies $ \_ ->
      let Right x = evaluate undefined [] 10000 (isaH integerTH (primIntegerH 1))
      in x
    
    insts :: [Term]
    insts = map ($ ()) $ replicate numCopies $ \_ ->
      let Right x = evaluate undefined [] 10000 (instH (abstH "a" (primIntegerH 1)) integerTH)
      in x
    
    apps :: [Term]
    apps = map ($ ()) $ replicate numCopies $ \_ ->
      let Right x = evaluate undefined [] 10000 (appH (lamH "x" (primIntegerH 1)) (primIntegerH 2))
      in x
    
    adds :: [Term]
    adds = map ($ ()) $ replicate numCopies $ \_ ->
      let Right x = evaluate undefined [] 10000 (builtinH "addInteger" [primIntegerH 1, primIntegerH 1])
      in x