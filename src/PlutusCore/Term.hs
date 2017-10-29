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

import PlutusShared.Qualified
-- import PlutusShared.Type
import Utils.ABT
-- import Utils.Names
import Utils.Pretty
-- import Utils.Vars

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

data TermF r
  = 
    
    -- Terms
    
    Decname QualifiedName
  | Isa r r
  | Abst r
  | Inst r r
  | Lam r
  | App r r
  | Con QualifiedConstructor [r]
  | Case r [ClauseF r]
  | Success r
  | Failure
  | CompBuiltin String
  | Bind r r
  | PrimInteger Integer
  | PrimFloat Float
  | PrimByteString BS.ByteString
  | Builtin String [r]
  
  
    -- Types
  
  | DecnameT QualifiedName
  | FunT r r
  | ConT QualifiedConstructor [r]
  | CompT r
  | ForallT Kind r
  | IntegerT
  | FloatT
  | ByteStringT
  | LamT Kind r
  | AppT r r
  
  deriving (Functor,Foldable,Traversable)


type Term = ABT TermF

isType :: Term -> Bool
isType (Var _) = True
isType (In (DecnameT _)) = True
isType (In (FunT _ _)) = True
isType (In (ConT _ _)) = True
isType (In (CompT _)) = True
isType (In (ForallT _ _)) = True
isType (In IntegerT) = True
isType (In FloatT) = True
isType (In ByteStringT) = True
isType (In (LamT _ _)) = True
isType (In (AppT _ _)) = True
isType _ = False

isTerm :: Term -> Bool
isTerm (Var _) = True
isTerm m = not (isType m)





-- | Clauses are a component of terms that have bunch of pattern scopes
-- together with a clause body.

data ClauseF r = Clause QualifiedConstructor r
  deriving (Functor,Foldable,Traversable)


type Clause = ClauseF (Scope TermF)






decnameH :: QualifiedName -> Term
decnameH n = In (Decname n)

isaH :: Term -> Term -> Term
isaH a m = In (Isa (scope [] a) (scope [] m))

abstH :: String -> Term -> Term
abstH x m = In (Abst (scope [x] m))

instH :: Term -> Term -> Term
instH m a = In (Inst (scope [] m) (scope [] a))

lamH :: String -> Term -> Term
lamH v b = In (Lam (scope [v] b))

appH :: Term -> Term -> Term
appH f x = In (App (scope [] f) (scope [] x))

conH :: QualifiedConstructor -> [Term] -> Term
conH c xs = In (Con c (map (scope []) xs))

caseH :: Term -> [Clause] -> Term
caseH a cs = In (Case (scope [] a) cs)

clauseH :: QualifiedConstructor -> [String] -> Term -> Clause
clauseH qc vs b = Clause qc (scope vs b)

successH :: Term -> Term
successH m = In (Success (scope [] m))

failureH :: Term
failureH = In Failure

compBuiltinH :: String -> Term
compBuiltinH n = In (CompBuiltin  n)
bindH :: Term -> String -> Term -> Term
bindH m x n = In (Bind (scope [] m) (scope [x] n))

primIntegerH :: Integer -> Term
primIntegerH x = In (PrimInteger x)

primFloatH :: Float -> Term
primFloatH x = In (PrimFloat x)

primByteStringH :: BS.ByteString -> Term
primByteStringH x = In (PrimByteString x)

builtinH :: String -> [Term] -> Term
builtinH n ms = In (Builtin n (map (scope []) ms))

decnameTH :: QualifiedName -> Term
decnameTH qn = In (DecnameT qn)

funTH :: Term -> Term -> Term
funTH a b = In (FunT (scope [] a) (scope [] b))

conTH :: QualifiedConstructor -> [Term] -> Term
conTH qc as = In (ConT qc (map (scope []) as))

compTH :: Term -> Term
compTH a = In (CompT (scope [] a))

forallTH :: String -> Kind -> Term -> Term
forallTH x k a = In (ForallT k (scope [x] a))

byteStringTH :: Term
byteStringTH = In ByteStringT

integerTH :: Term
integerTH = In IntegerT

floatTH :: Term
floatTH = In FloatT

lamTH :: String -> Kind -> Term -> Term
lamTH x k a = In (LamT k (scope [x] a))

appTH :: Term -> Term -> Term
appTH f a = In (AppT (scope [] f) (scope [] a))







-- | Terms have a variety of locations that can potentially be sites of
-- de-parenthesization.

instance Parens Term where
  type Loc Term = ()
  
  parenLoc _ = [()]
  
  parenRec (Var v) =
    name v
  parenRec (In (Decname n)) =
    prettyQualifiedName n
  parenRec (In (Isa a m)) =
    "(isa "
      ++ parenthesize Nothing (instantiate0 a)
      ++ " "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (In (Abst sc)) =
    "(abs "
      ++ head (names sc)
      ++ " "
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (In (Inst m a)) =
    "(inst "
      ++ parenthesize Nothing (instantiate0 m)
      ++ " "
      ++ parenthesize Nothing (instantiate0 a)
      ++ ")"
  parenRec (In (Lam sc)) =
    "(lam "
      ++ head (names sc)
      ++ " "
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (In (App f a)) =
    "["
      ++ parenthesize Nothing (instantiate0 f)
      ++ " "
      ++ parenthesize Nothing (instantiate0 a)
      ++ "]"
  parenRec (In (Con c as)) =
    "(con "
      ++ prettyQualifiedConstructor c
      ++ concat (map ((" " ++) . parenthesize Nothing . instantiate0) as)
      ++ ")"
  parenRec (In (Case a cs)) =
    "(case "
      ++ parenthesize Nothing (body a)
      ++ " "
      ++ unwords (map auxClause cs)
      ++ ")"
    where
      auxClause :: Clause -> String
      auxClause (Clause con sc) =
        "(cl "
        ++ prettyQualifiedConstructor con
        ++ " ("
        ++ unwords (names sc)
        ++ ") "
        ++ parenthesize Nothing (body sc)
        ++ ")"
  parenRec (In (Success m)) =
    "(success "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (In Failure ) =
    "(failure)"
  parenRec (In (CompBuiltin n)) =
    "(compbuiltin" ++ n ++ ")"
  parenRec (In (Bind m sc)) =
    "(bind "
    ++ parenthesize Nothing (instantiate0 m)
    ++ " "
    ++ head (names sc)
    ++ " "
    ++ parenthesize Nothing (body sc)
    ++ ")"
  parenRec (In (PrimInteger i)) =
    show i
  parenRec (In (PrimFloat f)) =
    show f
  parenRec (In (PrimByteString bs)) =
    prettyByteString bs
  parenRec (In (Builtin n ms)) =
    "(builtin "
      ++ n
      ++ " "
      ++ unwords (map (parenthesize Nothing . instantiate0) ms)
      ++ ")"
  parenRec (In (DecnameT qn)) =
    prettyQualifiedName qn
  parenRec (In (FunT a b)) =
    "(fun "
      ++ parenthesize Nothing (instantiate0 a)
      ++ " "
      ++ parenthesize Nothing (instantiate0 b)
      ++ ")"
  parenRec (In (ConT qc as)) =
    "(con "
      ++ prettyQualifiedConstructor qc
      ++ concat (map ((" " ++) . parenthesize Nothing . instantiate0) as)
      ++ ")"
  parenRec (In (CompT a)) =
    "(comp "
      ++ parenthesize Nothing (instantiate0 a)
      ++ ")"
  parenRec (In (ForallT k sc)) =
    "(forall "
      ++ head (names sc)
      ++ " "
      ++ prettyKind k
      ++ " "
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (In ByteStringT) =
    "(bytestring)"
  parenRec (In IntegerT) =
    "(integer)"
  parenRec (In FloatT) =
    "(float)"
  parenRec (In (LamT k sc)) =
    "(lam "
      ++ head (names sc)
      ++ " "
      ++ prettyKind k
      ++ " "
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (In (AppT f a)) =
    "["
      ++ parenthesize Nothing (instantiate0 f)
      ++ " "
      ++ parenthesize Nothing (instantiate0 a)
      ++ "]"