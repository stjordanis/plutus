{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}





-- | The terms of the simply typed lambda calculus w/ non-parametric user
-- defined types (eg Bool, Nat).

module PlutusCore.Term where

import PlutusShared.Qualified
import PlutusShared.Type
import Utils.ABT
import Utils.JSABT
import Utils.Names
import Utils.Pretty
import Utils.Vars

import Control.Monad.State
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Lazy.Char8 as BSChar8
import Data.Functor.Identity
import Data.List (intercalate)

import GHC.Generics hiding (Constructor)







data Kind = TypeK | FunK Kind Kind

instance ToJS Kind where
  toJS TypeK = JSABT "TypeK" []
  toJS (FunK k k') = JSABT "FunK" [toJS k, toJS k']

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
  | TxHash
  | BlockNum
  | BlockTime
  | Bind r r
  | PrimInt Int
  | PrimFloat Float
  | PrimByteString BS.ByteString
  | Builtin String [r]
  
  
    -- Types
  
  | DecnameT QualifiedName
  | FunT r r
  | ConT QualifiedConstructor [r]
  | CompT r
  | ForallT Kind r
  | ByteStringT
  | IntegerT
  | FloatT
  | LamT Kind r
  | AppT r r
  
  deriving (Functor,Foldable,Traversable,Generic)


type Term = ABT TermF






-- | Clauses are a component of terms that have bunch of pattern scopes
-- together with a clause body.

data ClauseF r = Clause QualifiedConstructor r
  deriving (Functor,Foldable,Traversable,Generic)


type Clause = ClauseF (Scope TermF)






decnameH :: QualifiedName -> Term
decnameH n = In (Decname n)

isaH :: Term -> Term -> Term
isaH m a = In (Isa (scope [] m) (scope [] a))

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

txhashH :: Term
txhashH = In TxHash

blocknumH :: Term
blocknumH = In BlockNum

blocktimeH :: Term
blocktimeH = In BlockTime

bindH :: Term -> String -> Term -> Term
bindH m x n = In (Bind (scope [] m) (scope [x] n))

primIntH :: Int -> Term
primIntH x = In (PrimInt x)

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
  parenRec (In (Isa m a)) =
    "(isa "
      ++ parenthesize Nothing (instantiate0 m)
      ++ " "
      ++ parenthesize Nothing (instantiate0 a)
      ++ ")"
  parenRec (In (Abst m)) =
    "(abs "
      ++ parenthesize Nothing (instantiate0 m)
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
      ++ " "
      ++ unwords (map (parenthesize Nothing . instantiate0) as)
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
  parenRec (In TxHash) =
    "(txhash)"
  parenRec (In BlockNum) =
    "(blocknum)"
  parenRec (In BlockTime) =
    "(blocktime)"
  parenRec (In (Bind m sc)) =
    "(bind "
    ++ parenthesize Nothing (instantiate0 m)
    ++ " "
    ++ head (names sc)
    ++ " "
    ++ parenthesize Nothing (body sc)
    ++ ")"
  parenRec (In (PrimInt i)) =
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
      ++ " "
      ++ unwords (map (parenthesize Nothing . instantiate0) as)
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







instance ToJS Term where
  toJS m0 = fst (runState (go m0) (0,[]))
    where
      getVar :: Int -> State (Int,[String]) String
      getVar i =
        do (_,ctx) <- get
           return (ctx !! i)
      
      withVar :: (String -> State (Int,[String]) a) -> State (Int,[String]) (String,a)
      withVar f =
        do (i,ctx) <- get
           let x = "x" ++ show i
           put (i+1, x : ctx)
           a <- f x
           (i',_) <- get
           put (i',ctx)
           return (x,a)
      
      withVars :: Int -> ([String] -> State (Int,[String]) a) -> State (Int,[String]) ([String],a)
      withVars n f =
        do (i,ctx) <- get
           let xs = [ "x" ++ show j | j <- [i..i+n-1] ]
           put (i+n, xs ++ ctx)
           a <- f xs
           put (i+n, ctx)
           return (xs,a)
      
      go :: Term -> State (Int,[String]) JSABT
      go (Var (Free _)) =
        error "There should never be free vars in a JS-able term."
      go (Var (Bound _ (BoundVar i))) =
        do x <- getVar i
           return (JSVar x)
      go (Var (Meta _)) =
        error "There should never be meta vars in a JS-able term."
      go (In (Decname n)) =
        return $ JSABT "Decname" [toJS n]
      go (In (Isa m a)) =
        do m' <- go (instantiate0 m)
           a' <- go (instantiate0 a)
           return $ JSABT "Isa" [m', a']
      go (In (Abst m)) =
        do m' <- go (instantiate0 m)
           return $ JSABT "Abs" [m']
      go (In (Inst m a)) =
        do m' <- go (instantiate0 m)
           a' <- go (instantiate0 a)
           return $ JSABT "Inst" [m', a']
      go (In (Lam sc)) =
        do (x,b) <- withVar $ \_ -> go (body sc)
           return $ JSABT "Lam" [JSScope [x] b]
      go (In (App f x)) =
        do f' <- go (instantiate0 f)
           x' <- go (instantiate0 x)
           return $ JSABT "App" [f',x']
      go (In (Con c ms)) =
        do ms' <- mapM (go . instantiate0) ms
           return $ JSABT "Con" [toJS c, JSArray ms']
      go (In (Case m cs)) =
        do m' <- go (instantiate0 m)
           cs' <- mapM goClause cs
           return $ JSABT "Case" [m', JSArray cs']
      go (In (Success m)) =
        do m' <- go (instantiate0 m)
           return $ JSABT "Success" [m']
      go (In Failure) =
        return $ JSABT "Failure" []
      go (In TxHash) =
        return $ JSABT "TxHash" []
      go (In BlockNum) =
        return $ JSABT "BlockNum" []
      go (In BlockTime) =
        return $ JSABT "BlockTime" []
      go (In (Bind m sc)) =
        do m' <- go (instantiate0 m)
           (x,b) <- withVar $ \_ -> go (body sc)
           return $ JSABT "Bind" [m', JSScope [x] b]
      go (In (PrimInt i)) =
        return $ JSABT "PrimInt" [JSInt i]
      go (In (PrimFloat f)) =
        return $ JSABT "PrimFloat" [JSFloat f]
      go (In (PrimByteString bs)) =
        return $ JSABT "PrimByteString" [JSString (BSChar8.unpack bs)]
      go (In (Builtin n ms)) =
        do ms' <- mapM (go . instantiate0) ms
           return $ JSABT "Builtin" [JSString n, JSArray ms']
      go (In (DecnameT qn)) =
        return $ JSABT "DecnameT" [toJS qn]
      go (In (FunT a b)) =
        do a' <- go (instantiate0 a)
           b' <- go (instantiate0 b)
           return $ JSABT "FunT" [a',b']
      go (In (ConT qc as)) =
        do as' <- mapM (go . instantiate0) as
           return $ JSABT "ConT" [toJS qc, JSArray as']
      go (In (CompT a)) =
        do a' <- go (instantiate0 a)
           return $ JSABT "CompT" [a']
      go (In (ForallT k sc)) =
        do (x,a) <- withVar $ \_ -> go (body sc)
           return $ JSABT "ForallT" [toJS k, JSScope [x] a]
      go (In ByteStringT) =
        return $ JSABT "ByteStringT" []
      go (In IntegerT) =
        return $ JSABT "IntegerT" []
      go (In FloatT) =
        return $ JSABT "FloatT" []
      go (In (LamT k sc)) =
        do (x,a) <- withVar $ \_ -> go (body sc)
           return $ JSABT "LamT" [toJS k, JSScope [x] a]
      go (In (AppT f a)) =
        do f' <- go (instantiate0 f)
           a' <- go (instantiate0 a)
           return $ JSABT "AppT" [f', a']
      
      goClause :: Clause -> State (Int,[String]) JSABT
      goClause (Clause c sc) =
        do (xs, b) <- withVars (length (names sc)) $ \_ ->
                        go (body sc)
           return $ JSABT "Clause" [toJS c, JSScope xs b]
