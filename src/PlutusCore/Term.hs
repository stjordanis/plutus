{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}





-- | The terms of the simply typed lambda calculus w/ non-parametric user
-- defined types (eg Bool, Nat).

module PlutusCore.Term where

-- import PlutusShared.Type
import Utils.ABT
-- import Utils.Names
import Utils.Pretty
import Utils.Vars

-- import Control.Monad.State
import qualified Data.ByteString.Lazy as BS
-- import qualified Data.ByteString.Lazy.Char8 as BSChar8
-- import Data.Functor.Identity
-- import Data.List (intercalate)







data Kind = TypeK | FunK Kind Kind
  deriving (Eq)

prettyKind :: Kind -> String
prettyKind TypeK = "(type)"
prettyKind (FunK k k') =
  "(fun "
    ++ prettyKind k
    ++ " "
    ++ prettyKind k'
    ++ ")"


-- | There are ten kinds of terms, declared names @decname[n]@, let
-- expressions @let(e1;x.e2)@, lambdas @lam(x.e)@, application @app(e1;e2)@,
-- constructor terms @con[n](e*)@, case expressions @case(e;c*)@, success
-- expressions @success(e)@, failure expressions @failure@, computation
-- binds @bind(e1;x.e2)@, and finally, built-ins @builtin[n](e*)@.

data PlutusSig
  = 
  
    Decname String
  
    
    -- Terms
    
  | Isa
  | Abst
  | Inst
  | Lam
  | App
  | Con String
  | Case
  | Wrap
  | Unwrap
  | Success
  | Failure
  | CompBuiltin String
  | Bind
  | PrimInteger Integer
  | PrimFloat Float
  | PrimByteString BS.ByteString
  | Builtin String
  
  
    -- Types
  
  | FunT
  | ConT String
  | CompT
  | ForallT Kind
  | FixT
  | IntegerT
  | FloatT
  | ByteStringT
  | LamT Kind
  | AppT
  
  
    -- Clauses
  
  | Clause String
  
  deriving (Eq)



type Term = ABT PlutusSig
type Type = ABT PlutusSig
type Clause = ABT PlutusSig



isType :: Type -> Bool
isType (Var _) = True
isType (c :$: _) = case c of
  Decname _ -> True
  FunT -> True
  ConT _ -> True
  CompT -> True
  ForallT _ -> True
  FixT -> True
  IntegerT -> True
  FloatT -> True
  ByteStringT -> True
  LamT _ -> True
  AppT -> True
  _ -> False

isTerm :: Term -> Bool
isTerm (Var _) = True
isTerm (Decname _ :$: []) = True
isTerm m = not (isType m)









decnameH :: String -> Term
decnameH n = Decname n :$: []

isaH :: Term -> Term -> Term
isaH a m = Isa :$: [scope [] a, scope [] m]

abstH :: String -> Term -> Term
abstH x m = Abst :$: [scope [x] m]

instH :: Term -> Term -> Term
instH m a = Inst :$: [scope [] m, scope [] a]

lamH :: String -> Term -> Term
lamH v b = Lam :$: [scope [v] b]

appH :: Term -> Term -> Term
appH f x = App :$: [scope [] f, scope [] x]

conH :: String -> [Term] -> Term
conH c xs = Con c :$: map (scope []) xs

caseH :: Term -> [Clause] -> Term
caseH a cs = Case :$: map (scope []) (a : cs)

clauseH :: String -> [String] -> Term -> Clause
clauseH c vs b = Clause c :$: [scope vs b]

wrapH :: Term -> Term
wrapH m = Wrap :$: [scope [] m]

unwrapH :: Term -> Term
unwrapH m = Unwrap :$: [scope [] m]

successH :: Term -> Term
successH m = Success :$: [scope [] m]

failureH :: Term
failureH = Failure :$: []

compBuiltinH :: String -> Term
compBuiltinH n = CompBuiltin  n :$: []

bindH :: Term -> String -> Term -> Term
bindH m x n = Bind :$: [scope [] m, scope [x] n]

primIntegerH :: Integer -> Term
primIntegerH x = PrimInteger x :$: []

primFloatH :: Float -> Term
primFloatH x = PrimFloat x :$: []

primByteStringH :: BS.ByteString -> Term
primByteStringH x = PrimByteString x :$: []

builtinH :: String -> [Term] -> Term
builtinH n ms = Builtin n :$: map (scope []) ms

funTH :: Term -> Term -> Term
funTH a b = FunT :$: [scope [] a, scope [] b]

conTH :: String -> [Term] -> Term
conTH c as = ConT c :$: map (scope []) as

compTH :: Term -> Term
compTH a = CompT :$: [scope [] a]

forallTH :: String -> Kind -> Term -> Term
forallTH x k a = ForallT k :$: [scope [x] a]

fixTH :: String -> Term -> Term
fixTH x a = FixT :$: [scope [x] a]

byteStringTH :: Term
byteStringTH = ByteStringT :$: []

integerTH :: Term
integerTH = IntegerT :$: []

floatTH :: Term
floatTH = FloatT :$: []

lamTH :: String -> Kind -> Term -> Term
lamTH x k a = LamT k :$: [scope [x] a]

appTH :: Term -> Term -> Term
appTH f a = AppT :$: [scope [] f, scope [] a]







-- | Terms have a variety of locations that can potentially be sites of
-- de-parenthesization.

instance Parens Term where
  type Loc Term = ()
  
  parenLoc _ = [()]
  
  parenRec (Var v) =
    name v
  parenRec (Decname n :$: _) =
    n
  parenRec (Isa :$: [a,m]) =
    "(isa "
      ++ parenthesize Nothing (instantiate0 a)
      ++ " "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (Abst :$: [sc]) =
    "(abs "
      ++ head (names sc)
      ++ " "
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (Inst :$: [m,a]) =
    "(inst "
      ++ parenthesize Nothing (instantiate0 m)
      ++ " "
      ++ parenthesize Nothing (instantiate0 a)
      ++ ")"
  parenRec (Lam :$: [sc]) =
    "(lam "
      ++ head (names sc)
      ++ " "
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (App :$: [f,a]) =
    "["
      ++ parenthesize Nothing (instantiate0 f)
      ++ " "
      ++ parenthesize Nothing (instantiate0 a)
      ++ "]"
  parenRec (Con c :$: as) =
    "(con "
      ++ c
      ++ concat (map ((" " ++) . parenthesize Nothing . instantiate0) as)
      ++ ")"
  parenRec (Case :$: (a:cs)) =
    "(case "
      ++ parenthesize Nothing (body a)
      ++ " "
      ++ unwords (map (parenthesize Nothing . instantiate0) cs)
      ++ ")"
  parenRec (Wrap :$: [m]) =
    "(wrap "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (Unwrap :$: [m]) =
    "(unwrap "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (Success :$: [m]) =
    "(success "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (Failure :$: []) =
    "(failure)"
  parenRec (CompBuiltin n :$: []) =
    "(compbuiltin" ++ n ++ ")"
  parenRec (Bind :$: [m,sc]) =
    "(bind "
    ++ parenthesize Nothing (instantiate0 m)
    ++ " "
    ++ head (names sc)
    ++ " "
    ++ parenthesize Nothing (body sc)
    ++ ")"
  parenRec (PrimInteger i :$: []) =
    show i
  parenRec (PrimFloat f :$: []) =
    show f
  parenRec (PrimByteString bs :$: []) =
    prettyByteString bs
  parenRec (Builtin n :$: ms) =
    "(builtin "
      ++ n
      ++ " "
      ++ unwords (map (parenthesize Nothing . instantiate0) ms)
      ++ ")"
  parenRec (FunT :$: [a,b]) =
    "(fun "
      ++ parenthesize Nothing (instantiate0 a)
      ++ " "
      ++ parenthesize Nothing (instantiate0 b)
      ++ ")"
  parenRec (ConT c :$: as) =
    "(con "
      ++ c
      ++ concat (map ((" " ++) . parenthesize Nothing . instantiate0) as)
      ++ ")"
  parenRec (CompT :$: [a]) =
    "(comp "
      ++ parenthesize Nothing (instantiate0 a)
      ++ ")"
  parenRec (ForallT k :$: [sc]) =
    "(forall "
      ++ head (names sc)
      ++ " "
      ++ prettyKind k
      ++ " "
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (FixT :$: [sc]) =
    "(fix "
      ++ head (names sc)
      ++ " "
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (ByteStringT :$: []) =
    "(bytestring)"
  parenRec (IntegerT :$: []) =
    "(integer)"
  parenRec (FloatT :$: []) =
    "(float)"
  parenRec (LamT k :$: [sc]) =
    "(lam "
      ++ head (names sc)
      ++ " "
      ++ prettyKind k
      ++ " "
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (AppT :$: [f,a]) =
    "["
      ++ parenthesize Nothing (instantiate0 f)
      ++ " "
      ++ parenthesize Nothing (instantiate0 a)
      ++ "]"
  parenRec (Clause c :$: [sc]) =
    "(" ++ c
        ++ " ("
        ++ unwords (names sc)
        ++ ") "
        ++ parenthesize Nothing (body sc)
        ++ ")"
  parenRec _ =
    error "You attempted to pretty print a syntactically ill-formed term. \
          \There should be no way to reach this case."