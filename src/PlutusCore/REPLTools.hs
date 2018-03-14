{-# OPTIONS -Wall #-}







module PlutusCore.REPLTools where

import PlutusCore.Contexts
import PlutusCore.Elaboration ()
import PlutusCore.Elaborator
import PlutusCore.Evaluation
import PlutusCore.EvaluatorTypes
import PlutusCore.Judgments
import PlutusCore.LanguageOptions
import PlutusCore.Parser
import PlutusCore.Program
import PlutusCore.REPLParser
import PlutusCore.REPLTypes
import PlutusCore.Term

import Utils.ABT hiding (names)
import Utils.Pretty
import qualified Utils.ProofDeveloper as PD

import Data.Char
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

invalidName :: String -> Bool
invalidName = not . all (\c -> isAlphaNum c || c == '_' || c == '\'')

emptyName :: String -> Bool
emptyName = all isSpace



quit :: IO ()
quit = flushLine "See you next time!"



evalAndPrintTerm :: LanguageOptions -> Program -> Environment -> Term -> IO ()
evalAndPrintTerm opts (Program decls) env m =
  case runElaborator
         opts
         (PD.proofDeveloper (SynthJ (Context decls []) m)) of
    Left e -> printError (PD.showProofError e)
    Right _ -> case evaluate undefined env 1000000 m of
      Left e' -> printError e'
      Right v -> flushLine (pretty v)

evalAndPrint :: LanguageOptions -> Program -> Environment -> String -> IO ()
evalAndPrint opts prog env s =
  case parseTerm "REPL (no source file)" s of
    Left e -> printError e
    Right m -> evalAndPrintTerm opts prog env (freeToDefined (\n -> Decname n :$: []) m)

getType :: LanguageOptions -> Program -> String -> IO ()
getType opts (Program decls) s =
  case parseTerm "REPL (no source file)" s of
    Left e -> printError e
    Right m ->
      case runElaborator
             opts
             (PD.proofDeveloper (SynthJ (Context decls []) m)) of
        Left e -> printError (PD.showProofError e)
        Right a -> flushLine (pretty a)

findNearestNames :: String -> Program -> [NameInfo]
findNearestNames tgt prog =
  [ ni
  | ni <- nameInfo prog
  , withinEditLimit (map toLower tgt)
                    (map toLower (nameInfoName ni))
  ]
  where
    editLimit = 3
    
    withinEditLimit n n' = isInfixOf n n' || goEditDistance 0 n n'
    
    goEditDistance d _ _ | d > editLimit = False
    goEditDistance _ [] [] = True
    goEditDistance d xs [] = d + length xs <= editLimit
    goEditDistance d [] ys = d + length ys <= editLimit
    goEditDistance d (x:xs) (y:ys)
      | x == y = goEditDistance d xs ys || rest
      | otherwise = rest
      where rest = goEditDistance (d+1) (x:xs) ys
                || goEditDistance (d+1) xs (y:ys)

getInfo :: Program -> String -> IO ()
getInfo prog@(Program decls) s =
  if invalidName s
  then printError ("Not a valid name: " ++ s)
  else if emptyName s
  then printError "Cannot get info on empty names."
  else if null matchingDeclarations
     then
       case findNearestNames s prog of
         [] ->
           printError
             ("There is no term named `" ++ s ++ "`, nor anything similar.")
         names ->
           do printError
                ("There is no term named `" ++ s ++ "`. Perhaps you meant one of the following:")
              forM_ names $ \ni -> flushLine ("  " ++ prettyNameInfo ni)
     else
       forM_ matchingDeclarations $ \decl ->
         do putStrLn (prettyDeclaration decl)
            putStrLn ""
  where
    matchingDeclarations =
      do decl <- decls
         case decl of
           DataDeclaration n _ alts
             | s == n || any (\(Alt n' _) -> s == n') alts ->
             [decl]
           TypeDeclaration n _ | s == n ->
             [decl]
           TermDeclaration n _ | s == n ->
             [decl]
           _ -> []
           

findName :: Program -> String -> IO ()
findName prog s =
  if invalidName s
  then printError ("Not a valid name: " ++ s)
  else if emptyName s
  then  printError "Cannot find empty names."
  else case names of
    [] ->
      flushLine ("There are no names similar to `" ++ s ++ "`.")
    _ ->
      do flushLine "Found names:"
         forM_ names $ \ni -> flushLine ("  " ++ prettyNameInfo ni)
  where
    names = findNearestNames s prog

invalid :: String -> IO ()
invalid s =
  printError ("Invalid REPL command: " ++ s)

evalAndPrintPrefixedOnValue :: LanguageOptions -> Program -> Environment -> String -> IO ()
evalAndPrintPrefixedOnValue opts prog env s =
  if invalidName s
  then printError ("Not a valid name: " ++ s)
  else if emptyName s
  then printError "Cannot evaluate empty names."
  else case parseNamePrefixThenTerm "REPL (no source file)" s of
    Left e -> printError e
    Right (pre,m) ->
      case namesWithNameAsPrefix prog pre of
        [] ->
          flushLine ("There are no terms beginning `" ++ pre ++ "'")
        ns -> forM_ ns $ \n ->
          do flushStr ("Testing " ++ n ++ ": ")
             evalAndPrintTerm opts prog env (appH (Decname n :$: []) m)

replLoop :: [String] -> LanguageOptions -> Program -> Environment -> IO ()
replLoop files opts prog env = hSetBuffering stdin LineBuffering >> continue
  where
    continue =
      do p <- readPrompt "PlutusCore> "
         case parseREPLCommand p of
           Empty ->
             continue
           Quit ->
             quit
           Reload ->
             replFiles files
           EvalPrefix str ->
             evalAndPrintPrefixedOnValue opts prog env str >> continue
           GetType str ->
             getType opts prog str >> continue
           GetInfo str ->
             getInfo prog str >> continue
           FindName str ->
             findName prog str >> continue
           Invalid str ->
             invalid str >> continue
           Eval str ->
             evalAndPrint opts prog env str >> continue
           

{-

data REPLCommand = Empty              -- all whitespace
                 | Quit               -- :q :quit
                 | Reload             -- :r :reload
                 | EvalPrefix String  -- :p :prefixEvaluate
                 | GetType String     -- :t :type
                 | GetInfo String     -- :i :info
                 | FindName String    -- :f :find
                 | Invalid String     -- :X for any other X
                 | Eval String        -- anything not of the form :X

-}

replFiles :: [String] -> IO ()
replFiles locs =
  do locsrcs <- forM locs $ \loc ->
                  do src <- readFile loc
                     return (loc,src)
     case mapM (uncurry parseProgramWithOptions) locsrcs of
       Left e -> printError e
       Right optprogs ->
         let (optss, progs) = unzip optprogs
         in if null optss || all (equivalent (head optss)) (tail optss)
            then let prog0 = Program (progs >>= (\(Program mods) -> mods))
                     opts = head optss
                 in case elabProgram opts prog0 of
                      Left e -> printError e
                      Right (prog,dctx) ->
                        {-# SCC "replLoopProf" #-} replLoop locs opts prog dctx
            else printError "Conflicting language options."
  where
    equivalent (LanguageOptions opts0) (LanguageOptions opts1) =
      sort (nub opts0) == sort (nub opts1)
    elabProgram opts prog =
      do mapLeft PD.showProofError
           (runElaborator
             opts
             (PD.proofDeveloper (ElabProgramJ prog) :: Elaborator ()))
         return (prog, extractDefinitions prog)         