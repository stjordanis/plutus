{-# OPTIONS -Wall #-}







module Testing.Testing where

import PlutusCore.Evaluation
import PlutusCore.EvaluatorTypes
import PlutusCore.Parser
import PlutusCore.Program
import PlutusShared.Qualified

import Utils.Pretty

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

repl :: String -> IO ()
repl src0 = case loadProgram src0 of
             Left e -> flushStr ("ERROR: " ++ e ++ "\n")
             Right dctx --(sig,defs,ctx)
               -> do hSetBuffering stdin LineBuffering
                     until_ (== ":quit")
                            (readPrompt "$> ")
                            (evalAndPrint dctx)
  where
    loadProgram
      :: String -> Either String QualifiedEnv
    loadProgram src =
      do prog <- parseProgram src
         return (extractDefinitions prog)
    
    {-
         (dctx,_)
           <- mapLeft PD.showElabError
                      (runElaborator
                        (PD.elaborator
                          (ElabProgram emptyDeclContext prog)))
         return dctx
    
    parseAndElab :: DeclContext -> String -> Either String (Core.Term,DeclContext)
    parseAndElab dctx src =
      do tm0 <- parseTerm src
         let tm = freeToDefined (In . Decname . User) tm0
         case runElaborator (PD.elaborator (Synth dctx emptyHypContext tm)) of
           Left e -> Left (PD.showElabError e)
           Right ((tm',_,dctx'),_) -> Right (tm',dctx')
    
    loadTerm :: DeclContext -> String -> Either String Core.Term
    loadTerm dctx src =
      do (tm',dctx') <- parseAndElab dctx src
         evaluate (TransactionInfo undefined {- !!! -})
                      (definitionsToEnvironment (definitions dctx'))
                      3750
                      tm'
    -}
    
    evalAndPrint :: QualifiedEnv -> String -> IO ()
    evalAndPrint env s =
      case parseTerm s of
        Left e -> flushStr ("ERROR: " ++ e ++ "\n")
        Right m ->
          case evaluate undefined env 10000 m of
            Left e -> flushStr ("ERROR: " ++ e ++ "\n")
            Right v -> flushStr (pretty v ++ "\n")
    
    {-
    evalAndPrint _ "" = return ()
    evalAndPrint dctx ":defs" =
      flushStr
        (unlines
          [ showSourced n
            | (n,_) <- definitions dctx
            ]
          ++ "\n")
    evalAndPrint dctx (':':'e':'l':'a':'b':src) =
      case parseAndElab dctx src of
        Left e -> flushStr ("ERROR: " ++ e ++ "\n")
        Right (m,_) -> flushStr (pretty m ++ "\n")
    evalAndPrint dctx (':':'j':'s':src) =
      case parseAndElab dctx src of
        Left e -> flushStr ("ERROR: " ++ e ++ "\n")
        Right (m,_) -> flushStr (jsABTToSource (toJS m) ++ "\n")
    evalAndPrint dctx src =
      case loadTerm dctx src of
        Left e -> flushStr ("ERROR: " ++ e ++ "\n")
        Right v -> flushStr (pretty v ++ "\n")
    -}


replFile :: String -> IO ()
replFile loc = readFile loc >>= repl
