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
import PlutusCore.Term
import PlutusShared.Qualified

import Utils.ABT
import Utils.Pretty
import qualified Utils.ProofDeveloper as PD

import Control.Monad
import Data.Either.Combinators (mapLeft)
import Data.List
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

flushLine :: String -> IO ()
flushLine str = flushStr (str ++ "\n")

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

printError :: String -> IO ()
printError e = flushLine ("ERROR: " ++ e)

evalAndPrintTerm :: Program -> QualifiedEnv -> Term -> IO ()
evalAndPrintTerm (Program ls) env m =
  case runElaborator
         (PD.elaborator (SynthJ (Context "Main"
                                         ["Prelude"]
                                         (ls,[])
                                         [])
                                m)) of
    Left e -> printError (PD.showElabError e)
    Right _ -> case evaluate undefined env 1000000 m of
      Left e' -> printError e'
      Right v -> flushLine (pretty v)

evalAndPrint :: Program -> QualifiedEnv -> String -> IO ()
evalAndPrint prog env s =
  case parseTerm s of
    Left e -> printError e
    Right m -> evalAndPrintTerm prog env m


data PromptCommand = Quit
                   | Evaluate String
                   | EvaluatePrefix String
                   | GetType String
                   | GetDefinition String

interpretPromptCommand :: String -> PromptCommand
interpretPromptCommand s =
  if isPrefixOf ":quit" s
  then Quit
  else case stripPrefix ":t " s of
    Just s' -> GetType s'
    Nothing -> case stripPrefix ":d " s of
      Just s' -> GetDefinition s'
      Nothing -> case stripPrefix ":p " s of
        Just s' -> EvaluatePrefix s'
        Nothing -> Evaluate s

getType :: Program -> String -> IO ()
getType prog s =
  case parseQualifiedName s of
    Left e -> printError e
    Right qn ->
      case typeForQualifiedName prog qn of
        Nothing ->
          printError ("There is no term named " ++ prettyQualifiedName qn)
        Just t ->
          flushLine (pretty t)

getDefinition :: Program -> String -> IO ()
getDefinition prog s =
  case parseQualifiedName s of
    Left e -> printError e
    Right qn ->
      case definitionForQualifiedName prog qn of
        Nothing ->
          printError ("There is no term named " ++ prettyQualifiedName qn)
        Just m ->
          flushLine (pretty m)

evalAndPrintPrefixedOnValue :: Program -> QualifiedEnv -> String -> IO ()
evalAndPrintPrefixedOnValue prog env s =
  case parseQualifiedNamePrefixThenTerm s of
    Left e -> printError e
    Right (qn,m) ->
      case namesWithQualifiedNameAsPrefix prog qn of
        [] ->
          flushLine ("There are no terms named " ++ prettyQualifiedName qn)
        ns -> forM_ ns $ \n ->
          do flushStr ("Testing " ++ prettyQualifiedName n ++ ": ")
             evalAndPrintTerm prog env (appH (Decname n :$: []) m)

replLoop :: Program -> QualifiedEnv -> IO ()
replLoop prog env = hSetBuffering stdin LineBuffering >> continue
  where
    continue =
      do p <- readPrompt "PlutusCore> "
         case interpretPromptCommand p of
           Quit -> flushLine "See you next time!"
           GetType s -> getType prog s >> continue
           GetDefinition s -> getDefinition prog s >> continue
           Evaluate s -> evalAndPrint prog env s >> continue
           EvaluatePrefix s -> evalAndPrintPrefixedOnValue prog env s >> continue

repl :: String -> IO ()
repl src0 = case loadProgram src0 of
             Left e -> printError e
             Right (prog,dctx) -> replLoop prog dctx
  where
    loadProgram
      :: String -> Either String (Program, QualifiedEnv)
    loadProgram src =
      do prog <- parseProgram src
         mapLeft PD.showElabError
           (runElaborator
             (PD.elaborator (ElabProgramJ prog) :: Elaborator ()))
         return (prog, extractDefinitions prog)

replFiles :: [String] -> IO ()
replFiles locs =
  do srcs <- mapM readFile locs
     case mapM parseProgram srcs of
       Left e -> printError e
       Right progs ->
         let prog0 = Program (progs >>= (\(Program mods) -> mods))
         in case elabProgram prog0 of
              Left e -> printError e
              Right (prog,dctx) -> {-# SCC "replLoopProf" #-} replLoop prog dctx
  where
    elabProgram prog =
      do mapLeft PD.showElabError
           (runElaborator
             (PD.elaborator (ElabProgramJ prog) :: Elaborator ()))
         return (prog, extractDefinitions prog)