{-# OPTIONS -Wall #-}







-- | This module defines the grammar for Plutus Core and the parser for that
-- grammar using the Parsec library.

module PlutusCore.Parser where

import PlutusCore.Term
import PlutusShared.Qualified
import Utils.ABT
import Utils.Vars

import qualified Data.ByteString.Lazy as BS
import Data.Char (digitToInt,toUpper)
import Data.Word
import Text.Parsec
import qualified Text.Parsec.Token as Token







-- | Plutus Core's syntax is s-expression based, intended to be as easy to
-- parse as possible. The grammar is given below in BNF.
--
--   <qualName> ::= "(" "qual" <moduleName> <termName> ")"
--   <qualCon> ::= "(" "qualcon" <moduleName> <conName> ")"
--   <term> ::= <variable>
--            | <decname>
--            | <letTerm>
--            | <lambda>
--            | <application>
--            | <conData>
--            | <caseTerm>
--            | <success>
--            | <failure>
--            | <txhash>
--            | <blocknum>
--            | <blocktime>
--            | <bindTerm>
--            | <primInt>
--            | <primFloat>
--            | <primByteString>
--            | <isFun>
--            | <isCon>
--            | <isConName>
--            | <isInt>
--            | <isFloat>
--            | <isByteString>
--   <decname> ::= "(" "decname" <qualName> ")"
--   <letTerm> ::= "(" "let" <term> <variable> <term> ")"
--   <lambda> ::= "(" "lam" <variable> <term> ")"
--   <application> ::= "(" "app" <term> <term> ")"
--   <conData> ::= "(" "con" <qualCon> <term>* ")"
--   <caseTerm> ::= "(" "case" <term> <clause>* ")"
--   <success> ::= "(" "success" <term> ")"
--   <failure> ::= "failure"
--   <txhash> ::= "txhash"
--   <blocknum> ::= "blocknum"
--   <blocktime> ::= "blocktime"
--   <bindTerm> ::= "(" "bind" <term> <variable> <term> ")"
--   <primInt> ::= "(" "primInt" <int> ")"
--   <primFloat> ::= "(" "primFloat" <float> ")"
--   <primByteString> ::= "(" "primByteString" <byteString> ")"
--   <isFun> ::= "(" "isFun" <term> ")"
--   <isCon> ::= "(" "isCon" <term> ")"
--   <isConName> ::= "(" "isConName" <qualCon> <term> ")"
--   <isInt> ::= "(" "isInt" <term> ")"
--   <isFloat> ::= "(" "isFloat" <term> ")"
--   <isByteString> ::= "(" "isByteString" <term> ")"

--   <clause> ::= "(" "cl" <qualCon> "(" <variable>* ")" <term> ")"
--   <program> ::= "(" "program" <module>* ")"
--   <module> ::= "(" "module" <moduleName> <declaration>* ")"
--   <declaration> ::= "(" "exp" <termName> <term> ")"
--                   | "(" "loc" <termName> <term> ")"
--                   | "(" "expcon" <conName> ")"
--                   | "(" "loccon" <conName> ")"





languageDef :: Token.LanguageDef st
languageDef = Token.LanguageDef
                { Token.commentStart = ";-"
                , Token.commentEnd = "-;"
                , Token.commentLine = ";;"
                , Token.nestedComments = True
                , Token.identStart = letter
                , Token.identLetter = alphaNum <|> char '_' <|> char '\''
                , Token.opStart = oneOf ""
                , Token.opLetter = oneOf ""
                , Token.reservedNames =
                    ["qual","qualcon"
                    ,"decname","let","lam","app","con","case","cl"
                    ,"success","failure","txhash","blocknum","blocktime","bind"
                    ,"primInt","primFloat","primByteString","builtin"
                    ,"isFun","isCon","isConName","isInt","isFloat","isByteString"
                    ,"program","module","exp","loc","expcon","loccon"
                    ]
                , Token.reservedOpNames = []
                , Token.caseSensitive = True
                }

tokenParser :: Token.TokenParser st
tokenParser = Token.makeTokenParser languageDef

lexeme :: Parsec String u a -> Parsec String u a
lexeme = Token.lexeme tokenParser

identifier :: Parsec String u String
identifier = Token.identifier tokenParser

reserved :: String -> Parsec String u ()
reserved = Token.reserved tokenParser

reservedOp :: String -> Parsec String u ()
reservedOp = Token.reservedOp tokenParser

parens :: Parsec String u a -> Parsec String u a
parens = Token.parens tokenParser

braces :: Parsec String u a -> Parsec String u a
braces = Token.braces tokenParser

whiteSpace :: Parsec String u ()
whiteSpace = Token.whiteSpace tokenParser





-- Parsers for literals

intLiteral :: Parsec String u Int
intLiteral = lexeme int <?> "int"

floatLiteral :: Parsec String u Float
floatLiteral = lexeme floating <?> "float"

byteStringLiteral :: Parsec String u BS.ByteString
byteStringLiteral =
  (lexeme $ do
     _ <- char '#'
     bytes <- many byte
     return (BS.pack bytes))
  <?> "byteString"

int :: Parsec String u Int
int =
  do f <- sign
     n <- decimal
     return (f n)

sign :: Num a => Parsec String u (a -> a)
sign =
      (char '-' >> return negate)
  <|> return id

decimal :: Parsec String u Int
decimal =
  do digits <- many1 digit
     let n = foldl (\x d -> 10*x + digitToInt d) 0 digits
     seq n (return n)

floating :: Parsec String u Float
floating =
  do n <- int
     fractExponent n

fractExponent :: Int -> Parsec String u Float
fractExponent n =
      (do fract <- fraction
          expo  <- option "" exponent'
          readFloat (show n ++ fract ++ expo))
  <|> (do expo <- exponent'
          readFloat (show n ++ expo))
  
  where
    readFloat s =
      case reads s of
        [(x, "")] -> return x
        _         -> parserZero

fraction :: Parsec String u String
fraction =
  (do _ <- char '.'
      digits <- many1 digit <?> "fraction"
      return ('.' : digits))
  <?> "fraction"

exponent' :: Parsec String u String
exponent' =
  (do _ <- oneOf "eE"
      sign' <- fmap (:[]) (oneOf "+-") <|> return ""
      e <- decimal <?> "exponent"
      return ('e' : sign' ++ show e))
  <?> "exponent"

byte :: Parsec String u Word8
byte =
  do x <- nybble
     y <- nybble
     return (16*x + y)

nybble :: Parsec String u Word8
nybble =
  do n <- hexDigit
     case toUpper n of
       '0' -> return 0
       '1' -> return 1
       '2' -> return 2
       '3' -> return 3
       '4' -> return 4
       '5' -> return 5
       '6' -> return 6
       '7' -> return 7
       '8' -> return 8
       '9' -> return 9
       'A' -> return 10
       'B' -> return 11
       'C' -> return 12
       'D' -> return 13
       'E' -> return 14
       'F' -> return 15
       x -> error $ "The character " ++ [x] ++ " is not a hexDigit. Something"
                 ++ " very wrong has happened."





term :: Parsec String u Term
term =
      variable
  <|> decname
  <|> letTerm
  <|> lambda
  <|> application
  <|> conData
  <|> caseTerm
  <|> success
  <|> failure
  <|> txhash
  <|> blocknum
  <|> blocktime
  <|> bindTerm
  <|> primInt
  <|> primFloat
  <|> primByteString
  <|> isFun
  <|> isCon
  <|> isConName
  <|> isInt
  <|> isFloat
  <|> isByteString





variableName :: Parsec String u String
variableName =
  do _ <- lookAhead (lower <|> char '_')
     identifier



termName :: Parsec String u String
termName =
  do _ <- lookAhead (lower <|> char '_')
     identifier



conName :: Parsec String u String
conName =
  do _ <- lookAhead upper
     identifier



moduleName :: Parsec String u String
moduleName =
  do _ <- lookAhead upper
     identifier



qualName :: Parsec String u QualifiedName
qualName =
  parens $ do
    reserved "qual"
    l <- moduleName
    n <- termName
    return $ QualifiedName l n



qualCon :: Parsec String u QualifiedConstructor
qualCon =
  parens $ do
    reserved "qualcon"
    l <- moduleName
    c <- conName
    return $ QualifiedConstructor l c



variable :: Parsec String u Term
variable =
  do x <- variableName
     return $ Var (Free (FreeVar x))



decname :: Parsec String u Term
decname =
  parens $ do
    reserved "decname"
    qn <- qualName
    return $ decnameH qn



letTerm :: Parsec String u Term
letTerm =
  parens $ do
    reserved "let"
    m <- term
    x <- variableName
    n <- term
    return $ letH m x n



lambda :: Parsec String u Term
lambda =
  parens $ do
    reserved "lam"
    x <- variableName
    m <- term
    return $ lamH x m



application :: Parsec String u Term
application =
  parens $ do
    reserved "app"
    m <- term
    n <- term
    return $ appH m n



conData :: Parsec String u Term
conData =
  parens $ do
    reserved "con"
    qc <- qualCon
    ms <- many term
    return $ conH qc ms



caseTerm :: Parsec String u Term
caseTerm =
  parens $ do
    reserved "case"
    m <- term
    cs <- many clause
    return $ caseH m cs



clause :: Parsec String u Clause
clause =
  parens $ do
    reserved "cl"
    qc <- qualCon
    xs <- parens (many variableName)
    m <- term
    return $ clauseH qc xs m



success :: Parsec String u Term
success =
  parens $ do
    reserved "success"
    m <- term
    return $ successH m



failure :: Parsec String u Term
failure =
  do reserved "failure"
     return failureH



txhash :: Parsec String u Term
txhash =
  do reserved "txhash"
     return txhashH



blocknum :: Parsec String u Term
blocknum =
  do reserved "blocknum"
     return blocknumH



blocktime :: Parsec String u Term
blocktime =
  do reserved "blocktime"
     return blocktimeH



bindTerm :: Parsec String u Term
bindTerm =
  parens $ do
    reserved "bind"
    m <- term
    x <- variableName
    n <- term
    return $ bindH m x n



primInt :: Parsec String u Term
primInt =
  parens $ do
    reserved "primInt"
    i <- intLiteral
    return $ primIntH i



primFloat :: Parsec String u Term
primFloat =
  parens $ do
    reserved "primFloat"
    f <- floatLiteral
    return $ primFloatH f



primByteString :: Parsec String u Term
primByteString =
  parens $ do
    reserved "primByteString"
    bs <- byteStringLiteral
    return $ primByteStringH bs



isFun :: Parsec String u Term
isFun =
  parens $ do
    reserved "isFun"
    m <- term
    return $ isFunH m



isCon :: Parsec String u Term
isCon =
  parens $ do
    reserved "isCon"
    m <- term
    return $ isConH m



isConName :: Parsec String u Term
isConName =
  parens $ do
    reserved "isConName"
    qc <- qualCon
    m <- term
    return $ isConNameH qc m



isInt :: Parsec String u Term
isInt =
  parens $ do
    reserved "isInt"
    m <- term
    return $ isIntH m



isFloat :: Parsec String u Term
isFloat =
  parens $ do
    reserved "isFloat"
    m <- term
    return $ isFloatH m



isByteString :: Parsec String u Term
isByteString =
  parens $ do
    reserved "isByteString"
    m <- term
    return $ isByteStringH m