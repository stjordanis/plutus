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

import Utils.ABT
import Utils.Pretty
import qualified Utils.ProofDeveloper as PD

import Control.Monad
import Data.Either.Combinators (mapLeft)
import Data.List
import System.IO





extractDefinitions :: Program -> Environment
extractDefinitions (Program decls) =
  decls >>= declToDefinitions
  where
    declToDefinitions :: Declaration -> Environment
    declToDefinitions (TermDefinition n v) = [(n , v)]
    declToDefinitions _ = []

flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

flushLine :: String -> IO ()
flushLine str = flushStr (str ++ "\n")

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

printError :: String -> IO ()
printError e = flushLine ("ERROR: " ++ e)

evalAndPrintTerm :: Program -> Environment -> Term -> IO ()
evalAndPrintTerm (Program decls) env m =
  case runElaborator
         (PD.elaborator (SynthJ (Context decls []) m)) of
    Left e -> printError (PD.showElabError e)
    Right _ -> case evaluate undefined env 1000000 m of
      Left e' -> printError e'
      Right v -> flushLine (pretty v)

evalAndPrint :: Program -> Environment -> String -> IO ()
evalAndPrint prog env s =
  case parseTerm s of
    Left e -> printError e
    Right m -> evalAndPrintTerm prog env (freeToDefined (\n -> Decname n :$: []) m)


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
  case parseName s of
    Left e -> printError e
    Right n ->
      case typeForName prog n of
        Nothing ->
          printError ("There is no term named " ++ n)
        Just t ->
          flushLine (pretty t)

getDefinition :: Program -> String -> IO ()
getDefinition prog s =
  case parseName s of
    Left e -> printError e
    Right n ->
      case definitionForName prog n of
        Nothing ->
          printError ("There is no term named " ++ n)
        Just m ->
          flushLine (pretty m)

evalAndPrintPrefixedOnValue :: Program -> Environment -> String -> IO ()
evalAndPrintPrefixedOnValue prog env s =
  case parseNamePrefixThenTerm s of
    Left e -> printError e
    Right (pre,m) ->
      case namesWithNameAsPrefix prog pre of
        [] ->
          flushLine ("There are no terms beginning `" ++ pre ++ "'")
        ns -> forM_ ns $ \n ->
          do flushStr ("Testing " ++ n ++ ": ")
             evalAndPrintTerm prog env (appH (Decname n :$: []) m)

replLoop :: Program -> Environment -> IO ()
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
      :: String -> Either String (Program, Environment)
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