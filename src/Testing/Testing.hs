{-# OPTIONS -Wall #-}







module Testing.Testing where

import PlutusCore.Contexts
import PlutusCore.Elaboration ()
import PlutusCore.Elaborator
import PlutusCore.Evaluation
import PlutusCore.EvaluatorTypes
import PlutusCore.Judgments
import PlutusCore.Parser
import PlutusCore.Program
import PlutusShared.Qualified

import Utils.Pretty
import qualified Utils.ProofDeveloper as PD

import Data.Either.Combinators (mapLeft)
import System.IO





extractDefinitions :: Program -> QualifiedEnv
extractDefinitions (Program modules) =
  modules >>= moduleToDefinitions
  where
    moduleToDefinitions :: Module -> QualifiedEnv
    moduleToDefinitions (Module l _ _ decls) =
      decls >>= declToDefinitions l
    
    declToDefinitions :: String -> Declaration -> QualifiedEnv
    declToDefinitions l (TermDefinition n v) =
      [(QualifiedName l n , v)]
    declToDefinitions _ _ = []

flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ p prompt action = do 
   result <- prompt
   if p result 
      then return ()
      else action result >> until_ p prompt action

evalAndPrint :: Program -> QualifiedEnv -> String -> IO ()
evalAndPrint (Program ls) env s =
  case parseTerm s of
    Left e -> flushStr ("ERROR: " ++ e ++ "\n")
    Right m ->
      case runElaborator
             (PD.elaborator (SynthJ (Context "Main"
                                             ["Prelude"]
                                             (ls,[])
                                             [])
                                    m)) of
        Left e -> flushStr ("ERROR: " ++ PD.showElabError e ++ "\n")
        Right _ -> case evaluate undefined env 10000 m of
          Left e' -> flushStr ("ERROR: " ++ e' ++ "\n")
          Right v -> flushStr (pretty v ++ "\n")

repl :: String -> IO ()
repl src0 = case loadProgram src0 of
             Left e -> flushStr ("ERROR: " ++ e ++ "\n")
             Right (prog,dctx) --(sig,defs,ctx)
               -> do hSetBuffering stdin LineBuffering
                     until_ (== ":quit")
                            (readPrompt "$> ")
                            (evalAndPrint prog dctx)
  where
    loadProgram
      :: String -> Either String (Program, QualifiedEnv)
    loadProgram src =
      do prog <- parseProgram src
         mapLeft PD.showElabError
           (runElaborator
             (PD.elaborator (ElabProgramJ prog) :: Elaborator ()))
         return (prog, extractDefinitions prog)


replFile :: String -> IO ()
replFile loc = readFile loc >>= repl

replFileWithPrelude :: String -> String -> IO ()
replFileWithPrelude preludeLoc loc =
  do prelude <- readFile preludeLoc
     code <- readFile loc
     case (parseProgram prelude, parseProgram code) of
       (Right (Program ls), Right (Program ls')) ->
         case elabProgram (Program (ls ++ ls')) of
           Left e -> flushStr ("ERROR: " ++ e ++ "\n")
           Right (prog,dctx) ->
             do hSetBuffering stdin LineBuffering
                until_ (== ":quit")
                       (readPrompt "$> ")
                       (evalAndPrint prog dctx)
       (Right _, Left e) -> flushStr ("ERROR: " ++ e ++ "\n")
       (Left e, _) -> flushStr ("ERROR: " ++ e ++ "\n")
  where
    elabProgram prog =
      do mapLeft PD.showElabError
           (runElaborator
             (PD.elaborator (ElabProgramJ prog) :: Elaborator ()))
         return (prog, extractDefinitions prog)