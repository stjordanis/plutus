{-# OPTIONS -Wall #-}





module PlutusCore.REPLParser where

import PlutusCore.REPLTypes

import Text.Parsec hiding (Empty)










parseREPLCommand :: String -> REPLCommand
parseREPLCommand str =
  case parse (spaces *> replCommand) "REPL (no source file)" str of
    Left _ -> Eval str
    Right cmd -> cmd



replCommand :: Parsec String u REPLCommand
replCommand = emptyCommand
          <|> namedCommand
          <|> evalCommand


  




emptyCommand :: Parsec String u REPLCommand
emptyCommand =
  do try (spaces >> eof)
     return Empty

namedCommand :: Parsec String u REPLCommand
namedCommand =
  do _ <- try (char ':')
     cmd <- many1 letter
     spaces
     case cmd of
       
       "q"    -> quitCommand
       "quit" -> quitCommand
       
       "r"      -> reloadCommand
       "reload" -> reloadCommand
       
       "ep"         -> evalPrefixCommand
       "evalPrefix" -> evalPrefixCommand
       
       "t"    -> getTypeCommand
       "type" -> getTypeCommand
       
       "i"    -> getInfoCommand
       "info" -> getInfoCommand
       
       "f"    -> findNameCommand
       "find" -> findNameCommand
       
       _ -> return (Invalid cmd)

evalCommand :: Parsec String u REPLCommand
evalCommand =
  do str <- many anyToken
     eof
     return (Eval str)




quitCommand :: Parsec String u REPLCommand
quitCommand = return Quit

reloadCommand :: Parsec String u REPLCommand
reloadCommand = return Reload

evalPrefixCommand :: Parsec String u REPLCommand
evalPrefixCommand =
  do str <- many anyToken
     eof
     return (EvalPrefix str)

getTypeCommand :: Parsec String u REPLCommand
getTypeCommand =
  do str <- many anyToken
     eof
     return (GetType str)

getInfoCommand :: Parsec String u REPLCommand
getInfoCommand =
  do str <- many anyToken
     eof
     return (GetInfo str)

findNameCommand :: Parsec String u REPLCommand
findNameCommand =
  do str <- many anyToken
     eof
     return (FindName str)