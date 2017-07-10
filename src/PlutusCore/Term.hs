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





-- | There are ten kinds of terms, declared names @decname[n]@, let
-- expressions @let(e1;x.e2)@, lambdas @lam(x.e)@, application @app(e1;e2)@,
-- constructor terms @con[n](e*)@, case expressions @case(e;c*)@, success
-- expressions @success(e)@, failure expressions @failure@, computation
-- binds @bind(e1;x.e2)@, and finally, built-ins @builtin[n](e*)@.

data TermF r
  = Decname QualifiedName
  | Let r r
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
  | IsFun r
  | IsCon r
  | IsConName QualifiedConstructor r
  | IsInt r
  | IsFloat r
  | IsByteString r
  deriving (Functor,Foldable,Traversable,Generic)


type Term = ABT TermF






-- | Clauses are a component of terms that have bunch of pattern scopes
-- together with a clause body.

data ClauseF r = Clause QualifiedConstructor r
  deriving (Functor,Foldable,Traversable,Generic)


type Clause = ClauseF (Scope TermF)






decnameH :: QualifiedName -> Term
decnameH n = In (Decname n)

letH :: Term -> String -> Term -> Term
letH m x n = In (Let (scope [] m) (scope [x] n))

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

isFunH :: Term -> Term
isFunH m = In (IsFun (scope [] m))

isConH :: Term -> Term
isConH m = In (IsCon (scope [] m))

isConNameH :: QualifiedConstructor -> Term -> Term
isConNameH qc m = In (IsConName qc (scope [] m))

isIntH :: Term -> Term
isIntH m = In (IsInt (scope [] m))

isFloatH :: Term -> Term
isFloatH m = In (IsFloat (scope [] m))

isByteStringH :: Term -> Term
isByteStringH m = In (IsByteString (scope [] m))





-- | Terms have a variety of locations that can potentially be sites of
-- de-parenthesization.

instance Parens Term where
  type Loc Term = ()
  
  parenLoc _ = [()]
  
  parenRec (Var v) =
    name v
  parenRec (In (Decname n)) =
    "(defined " ++ prettyQualifiedName n
      ++ ")"
  parenRec (In (Let m n)) =
    "(let "
    ++ parenthesize Nothing (instantiate0 m)
    ++ " "
    ++ head (names n)
    ++ " "
    ++ parenthesize Nothing (body n)
    ++ ")"
  parenRec (In (Lam sc)) =
    "(lam "
      ++ head (names sc)
      ++ " "
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (In (App f a)) =
    "(app "
      ++ parenthesize Nothing (instantiate0 f)
      ++ " "
      ++ parenthesize Nothing (instantiate0 a)
      ++ ")"
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
    "failure"
  parenRec (In TxHash) =
    "txhash"
  parenRec (In BlockNum) =
    "blocknum"
  parenRec (In BlockTime) =
    "blocktime"
  parenRec (In (Bind m sc)) =
    "(bind "
    ++ parenthesize Nothing (instantiate0 m)
    ++ " "
    ++ head (names sc)
    ++ " "
    ++ parenthesize Nothing (body sc)
    ++ ")"
  parenRec (In (PrimInt i)) =
    "(primInt "
      ++ show i
      ++ ")"
  parenRec (In (PrimFloat f)) =
    "(primFloat "
      ++ show f
      ++ ")"
  parenRec (In (PrimByteString bs)) =
    "(primByteString "
      ++ prettyByteString bs
      ++ ")"
  parenRec (In (Builtin n ms)) =
    "(buildin "
      ++ n
      ++ " "
      ++ unwords (map (parenthesize Nothing . instantiate0) ms)
      ++ ")"
  parenRec (In (IsFun m)) =
    "(isFun "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (In (IsCon m)) =
    "(isCon "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (In (IsConName qc m)) =
    "(isConName "
      ++ prettyQualifiedConstructor qc
      ++ " "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (In (IsInt m)) =
    "(isInt "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (In (IsFloat m)) =
    "(isFloat "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (In (IsByteString m)) =
    "(isByteString "
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"







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
      go (In (Let m sc)) =
        do m' <- go (instantiate0 m)
           (x,b) <- withVar $ \_ -> go (body sc)
           return $ JSABT "Let" [m', JSScope [x] b]
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
      go (In (IsFun m)) =
        do m' <- go (instantiate0 m)
           return $ JSABT "IsFun" [m']
      go (In (IsCon m)) =
        do m' <- go (instantiate0 m)
           return $ JSABT "IsCon" [m']
      go (In (IsConName qc m)) =
        do m' <- go (instantiate0 m)
           return $ JSABT "IsConName" [toJS qc, m']
      go (In (IsInt m)) =
        do m' <- go (instantiate0 m)
           return $ JSABT "IsInt" [m']
      go (In (IsFloat m)) =
        do m' <- go (instantiate0 m)
           return $ JSABT "IsFloat" [m']
      go (In (IsByteString m)) =
        do m' <- go (instantiate0 m)
           return $ JSABT "IsByteString" [m']
      
      goClause :: Clause -> State (Int,[String]) JSABT
      goClause (Clause c sc) =
        do (xs, b) <- withVars (length (names sc)) $ \_ ->
                        go (body sc)
           return $ JSABT "Clause" [toJS c, JSScope xs b]
