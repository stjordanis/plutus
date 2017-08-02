{-# OPTIONS -Wall #-}







-- | This module defines the grammar for Plutus Core and the parser for that
-- grammar using the Parsec library.

module PlutusCore.Parser where

import PlutusCore.Program
import PlutusCore.Term
import PlutusShared.Qualified
import Utils.ABT
import Utils.Vars

import qualified Data.ByteString.Lazy as BS
import Data.Char (digitToInt,toUpper)
import Data.List (foldl')
import Data.Word
import Text.Parsec
import qualified Text.Parsec.Token as Token











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
                , Token.reservedOpNames = ["."]
                , Token.caseSensitive = True
                }

tokenParser :: Token.TokenParser st
tokenParser = Token.makeTokenParser languageDef

symbol :: String -> Parsec String u String
symbol = Token.symbol tokenParser

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

brackets :: Parsec String u a -> Parsec String u a
brackets = Token.brackets tokenParser

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






variableName :: Parsec String u String
variableName =
  lexeme $ do
    first <- lower
    rest <- many (alphaNum <|> oneOf "_'")
    return $ first:rest



declaredName :: Parsec String u String
declaredName =
  lexeme $ do
    first <- lower
    rest <- many (alphaNum <|> oneOf "_'")
    return $ first:rest



conName :: Parsec String u String
conName =
  lexeme $ do
    first <- upper
    rest <- many (alphaNum <|> oneOf "_'")
    return $ first:rest



moduleName :: Parsec String u String
moduleName =
  lexeme $ do
    first <- upper
    rest <- many (alphaNum <|> oneOf "_'")
    return $ first:rest



qualName :: Parsec String u QualifiedName
qualName =
  lexeme $ do
    l <- moduleName
    reservedOp "."
    n <- declaredName
    return $ QualifiedName l n



qualCon :: Parsec String u QualifiedConstructor
qualCon =
  lexeme $ do
    l <- moduleName
    reservedOp "."
    c <- conName
    return $ QualifiedConstructor l c






construct :: String -> Parsec String u a -> Parsec String u a
construct n p =
  do try $ do
       _ <- symbol "("
       _ <- symbol n
       return ()
     x <- p
     _ <- symbol ")"
     return x






term :: Parsec String u Term
term =
      variable
  <|> decname
  <|> annotation
  <|> abst
  <|> inst
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
  <|> primFloat
  <|> primInt
  <|> primByteString
  <|> builtin





variable :: Parsec String u Term
variable =
  do x <- variableName
     return $ Var (Free (FreeVar x))



decname :: Parsec String u Term
decname =
  do qn <- qualName
     return $ decnameH qn



annotation :: Parsec String u Term
annotation =
  construct "isa" $ do
    m <- term
    t <- typep
    return $ isaH m t



abst :: Parsec String u Term
abst =
  construct "abs" $ do
    x <- variableName
    m <- term
    return $ abstH x m



inst :: Parsec String u Term
inst =
  construct "inst" $ do
    m <- term
    a <- typep
    return $ instH m a



lambda :: Parsec String u Term
lambda =
  construct "lam" $ do
    x <- variableName
    m <- term
    return $ lamH x m



application :: Parsec String u Term
application =
  brackets $ do
    m <- term
    ns <- many1 term
    return $ foldl' appH m ns



conData :: Parsec String u Term
conData =
  construct "con" $ do
    qc <- qualCon
    ms <- many term
    return $ conH qc ms



caseTerm :: Parsec String u Term
caseTerm =
  construct "case" $ do
    m <- term
    cs <- many clause
    return $ caseH m cs



clause :: Parsec String u Clause
clause =
  parens $ do
    qc <- qualCon
    xs <- parens (many variableName)
    m <- term
    return $ clauseH qc xs m



success :: Parsec String u Term
success =
  construct "success" $ do
    m <- term
    return $ successH m



failure :: Parsec String u Term
failure =
  construct "failure" $ do
    return failureH



txhash :: Parsec String u Term
txhash =
  construct "txhash" $ do
    return txhashH



blocknum :: Parsec String u Term
blocknum =
  construct "blocknum" $ do
    return blocknumH



blocktime :: Parsec String u Term
blocktime =
  construct "blocktime" $ do
    return blocktimeH



bindTerm :: Parsec String u Term
bindTerm =
  construct "bind" $ do
    m <- term
    x <- variableName
    n <- term
    return $ bindH m x n



primInt :: Parsec String u Term
primInt =
  do i <- intLiteral
     return $ primIntH i



primFloat :: Parsec String u Term
primFloat =
  do f <- try floatLiteral
     return $ primFloatH f



primByteString :: Parsec String u Term
primByteString =
  do bs <- byteStringLiteral
     return $ primByteStringH bs

builtin :: Parsec String u Term
builtin =
  construct "builtin" $ do
    x <- variableName
    ns <- many term
    return $ builtinH x ns


typep :: Parsec String u Term
typep =
      variableT
  <|> funT
  <|> conT
  <|> compT
  <|> forallT
  <|> bytestringT
  <|> integerT
  <|> floatT
  <|> lamT
  <|> appT

variableT :: Parsec String u Term
variableT =
  do x <- variableName
     return $ Var (Free (FreeVar x))

funT :: Parsec String u Term
funT =
  construct "fun" $ do
    a <- typep
    b <- typep
    return $ funTH a b

conT :: Parsec String u Term
conT =
  construct "con" $ do
    qc <- qualCon
    as <- many typep
    return $ conTH qc as

compT :: Parsec String u Term
compT =
  construct "comp" $ do
    a <- typep
    return $ compTH a

forallT :: Parsec String u Term
forallT =
  construct "forall" $ do
    x <- variableName
    k <- kind
    a <- typep
    return $ forallTH x k a

bytestringT :: Parsec String u Term
bytestringT =
  construct "bytestring" $ do
    return $ byteStringTH

integerT :: Parsec String u Term
integerT =
  construct "integer" $ do
    return $ integerTH

floatT :: Parsec String u Term
floatT =
  construct "float" $ do
    return $ floatTH

lamT :: Parsec String u Term
lamT =
  construct "lam" $ do
    x <- variableName
    k <- kind
    a <- typep
    return $ lamTH x k a

appT :: Parsec String u Term
appT =
  brackets $ do
    f <- typep
    as <- many1 typep
    return $ foldl' appTH f as


kind :: Parsec String u Kind
kind =
      typeK
  <|> funK

typeK :: Parsec String u Kind
typeK =
  construct "type" $ do
    return $ TypeK

funK :: Parsec String u Kind
funK =
  construct "fun" $ do
    k <- kind
    k' <- kind
    return $ FunK k k'




program :: Parsec String u Program
program =
  construct "program" $ do
    ls <- many modle
    return $ Program ls


modle :: Parsec String u Module
modle =
  construct "module" $ do
    l <- moduleName
    impd <- imprts
    expd <- exprts
    decls <- many declaration
    return $ Module l impd expd decls


imprts :: Parsec String u Imports
imprts =
  construct "imported" $ do
    ls <- many moduleName
    return ls


exprts :: Parsec String u Exports
exprts =
  construct "exported" $ do
    typeExports <- parens (many typeExport)
    ns <- parens (many variableName)
    return $ Exports typeExports ns



typeExport :: Parsec String u TypeExport
typeExport =
      typeNameExport
  <|> typeConstructorExport



typeNameExport :: Parsec String u TypeExport
typeNameExport =
  do x <- declaredName
     return $ TypeNameExport x



typeConstructorExport :: Parsec String u TypeExport
typeConstructorExport =
  parens $ do
    c <- conName
    cs <- parens (many conName)
    return $ TypeConstructorExport c cs



declaration :: Parsec String u Declaration
declaration =
      dataDeclaration
  <|> typeDeclaration
  <|> termDeclaration
  <|> termDefinition



dataDeclaration :: Parsec String u Declaration
dataDeclaration =
  construct "data" $ do
    c <- conName
    ks <- parens (many kindsig)
    alts <- many alt
    return $ DataDeclaration c ks alts

kindsig :: Parsec String u KindSig
kindsig =
  parens $ do
    x <- variableName
    k <- kind
    return $ KindSig x k

alt :: Parsec String u Alt
alt =
  parens $ do
    c <- conName
    ts <- many typep
    return $ Alt c ts

typeDeclaration :: Parsec String u Declaration
typeDeclaration =
  construct "type" $ do
    n <- declaredName
    tv <- typep
    return $ TypeDeclaration n tv


termDeclaration :: Parsec String u Declaration
termDeclaration =
  construct "declare" $ do
    n <- declaredName
    t <- typep
    return $ TermDeclaration n t

termDefinition :: Parsec String u Declaration
termDefinition =
  construct "define" $ do
    n <- declaredName
    v <- term
    return $ TermDefinition n v






parseProgram :: String -> Either String Program
parseProgram str =
  case parse (whiteSpace *> program <* eof) "(unknown)" str of
    Left e -> Left (show e)
    Right p -> Right p

parseTerm :: String -> Either String Term
parseTerm str =
  case parse (whiteSpace *> term <* eof) "(unknown)" str of
    Left e -> Left (show e)
    Right p -> Right p