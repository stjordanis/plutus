{-# OPTIONS -Wall #-}







module Testing.Testing where

import PlutusCore.Contexts
import PlutusCore.Elaboration ()
import PlutusCore.Elaborator
import PlutusCore.Evaluation
import PlutusCore.EvaluatorTypes
import PlutusCore.Judgments
import PlutusCore.LanguageOptions
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

evalAndPrintTerm :: LanguageOptions -> Program -> Environment -> Term -> IO ()
evalAndPrintTerm opts (Program decls) env m =
  case runElaborator
         opts
         (PD.elaborator (SynthJ (Context decls []) m)) of
    Left e -> printError (PD.showElabError e)
    Right _ -> case evaluate undefined env 1000000 m of
      Left e' -> printError e'
      Right v -> flushLine (pretty v)

evalAndPrint :: LanguageOptions -> Program -> Environment -> String -> IO ()
evalAndPrint opts prog env s =
  case parseTerm s of
    Left e -> printError e
    Right m -> evalAndPrintTerm opts prog env (freeToDefined (\n -> Decname n :$: []) m)


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

evalAndPrintPrefixedOnValue :: LanguageOptions -> Program -> Environment -> String -> IO ()
evalAndPrintPrefixedOnValue opts prog env s =
  case parseNamePrefixThenTerm s of
    Left e -> printError e
    Right (pre,m) ->
      case namesWithNameAsPrefix prog pre of
        [] ->
          flushLine ("There are no terms beginning `" ++ pre ++ "'")
        ns -> forM_ ns $ \n ->
          do flushStr ("Testing " ++ n ++ ": ")
             evalAndPrintTerm opts prog env (appH (Decname n :$: []) m)

replLoop :: LanguageOptions -> Program -> Environment -> IO ()
replLoop opts prog env = hSetBuffering stdin LineBuffering >> continue
  where
    continue =
      do p <- readPrompt "PlutusCore> "
         case interpretPromptCommand p of
           Quit -> flushLine "See you next time!"
           GetType s -> getType prog s >> continue
           GetDefinition s -> getDefinition prog s >> continue
           Evaluate s -> evalAndPrint opts prog env s >> continue
           EvaluatePrefix s -> evalAndPrintPrefixedOnValue opts prog env s >> continue

repl :: String -> IO ()
repl src0 = case loadProgram src0 of
             Left e -> printError e
             Right ((opts,prog),dctx) -> replLoop opts prog dctx
  where
    loadProgram
      :: String -> Either String ((LanguageOptions, Program), Environment)
    loadProgram src =
      do (opts,prog) <- parseProgramWithOptions src
         mapLeft PD.showElabError
           (runElaborator
             opts
             (PD.elaborator (ElabProgramJ prog) :: Elaborator ()))
         return ((opts,prog), extractDefinitions prog)

replFiles :: [String] -> IO ()
replFiles locs =
  do srcs <- mapM readFile locs
     case mapM parseProgramWithOptions srcs of
       Left e -> printError e
       Right optprogs ->
         let (optss, progs) = unzip optprogs
         in case optss of
              opts:optss' | all (equivalent opts) optss' ->
                let prog0 = Program (progs >>= (\(Program mods) -> mods))
                in case elabProgram opts prog0 of
                     Left e -> printError e
                     Right (prog,dctx) -> {-# SCC "replLoopProf" #-} replLoop opts prog dctx
              _ -> printError "Conflicting language options."
  where
    equivalent (LanguageOptions opts0) (LanguageOptions opts1) =
      sort (nub opts0) == sort (nub opts1)
    elabProgram opts prog =
      do mapLeft PD.showElabError
           (runElaborator
             opts
             (PD.elaborator (ElabProgramJ prog) :: Elaborator ()))
         return (prog, extractDefinitions prog)