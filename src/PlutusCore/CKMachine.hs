{-# OPTIONS -Wall #-}






module PlutusCore.CKMachine where

import PlutusCore.BuiltinEvaluation
import PlutusCore.EvaluatorTypes
import PlutusCore.PatternMatching
import PlutusCore.Term
import PlutusShared.BoolToTerm
import PlutusShared.Qualified
import Utils.ABT
import Utils.Env
import Utils.Names
import Utils.Pretty

import qualified Data.ByteString.Lazy as BS







data CKFrame = InIsaL Term
             | InIsaR Term
             | InAbst
             | InInstL Term
             | InInstR Term
             | InAppLeft Term
             | InAppRight Term
             | InCon QualifiedConstructor [Term] [Term]
             | InCase [ClauseF (Scope TermF)]
             | InSuccess
             | InBind (Scope TermF)
             | InBuiltin String [Term] [Term]
             | InFunTL Term
             | InFunTR Term
             | InConT QualifiedConstructor [Term] [Term]
             | InCompT
             | InAppTL Term
             | InAppTR Term

type CKStack = [CKFrame]

data BlockChainInfo =
     BlockChainInfo
     { transactionHash :: BS.ByteString
     , blockNumber :: Int
     , blockTime :: Int
     }





rec :: Petrol -> BlockChainInfo -> QualifiedEnv -> CKStack -> Term -> Either String Term
rec 0 _ _ _ _ = Left "Out of petrol."
rec _ _ _ _ (Var x) =
  Left ("Unbound variable: " ++ name x)
rec petrol bci denv stk (In (Decname n)) =
  case lookup n denv of
    Nothing ->
      Left ("Unknown constant/defined term: " ++ prettyQualifiedName n)
    Just m ->
      ret (petrol - 1) bci denv stk m
rec petrol bci denv stk (In (Isa m a)) =
  rec (petrol - 1) bci denv (InIsaL (instantiate0 a) : stk) (instantiate0 m)
rec petrol bci denv stk (In (Abst m)) =
  rec (petrol - 1) bci denv (InAbst: stk) (instantiate0 m)
rec petrol bci denv stk (In (Inst m a)) =
  rec (petrol - 1) bci denv (InInstL (instantiate0 a) : stk) (instantiate0 m)
rec petrol bci denv stk m@(In (Lam _)) =
  ret (petrol - 1) bci denv stk m
rec petrol bci denv stk (In (App f x)) =
  rec (petrol - 1) bci denv (InAppLeft (instantiate0 x) : stk) (instantiate0 f)
rec petrol bci denv stk m@(In (Con _ [])) =
  ret (petrol - 1) bci denv stk m
rec petrol bci denv stk (In (Con c (m:ms))) =
  rec (petrol - 1) bci denv (InCon c [] (map instantiate0 ms) : stk) (instantiate0 m)
rec petrol bci denv stk (In (Case m cs)) =
  rec (petrol - 1) bci denv (InCase cs : stk) (instantiate0 m)
rec petrol bci denv stk (In (Success m)) =
  rec (petrol - 1) bci denv (InSuccess : stk) (instantiate0 m)
rec petrol bci denv stk m@(In Failure) =
  ret (petrol - 1) bci denv stk m
rec petrol bci denv stk (In TxHash) =
  ret (petrol - 1) bci denv stk (primByteStringH (transactionHash bci))
rec petrol bci denv stk (In BlockNum) =
  ret (petrol - 1) bci denv stk (primIntH (blockNumber bci))
rec petrol bci denv stk (In BlockTime) =
  ret (petrol - 1) bci denv stk (primIntH (blockTime bci))
rec petrol bci denv stk (In (Bind m sc)) =
  rec (petrol - 1) bci denv (InBind sc : stk) (instantiate0 m)
rec petrol bci denv stk m@(In (PrimInt _)) =
  ret (petrol - 1) bci denv stk m
rec petrol bci denv stk m@(In (PrimFloat _)) =
  ret (petrol - 1) bci denv stk m
rec petrol bci denv stk m@(In (PrimByteString _)) =
  ret (petrol - 1) bci denv stk m
rec petrol bci denv stk (In (Builtin n [])) =
  case builtin n [] of
    Left err ->
      Left err
    Right m' ->
      ret (petrol - 1) bci denv stk m'
rec petrol bci denv stk (In (Builtin n (m:ms))) =
  rec (petrol - 1) bci denv (InBuiltin n [] (map instantiate0 ms) : stk) (instantiate0 m)
rec petrol bci denv stk (In (DecnameT qn)) =
  ret (petrol - 1) bci denv stk (In (DecnameT qn))
rec petrol bci denv stk (In (FunT a b)) =
  rec (petrol - 1) bci denv (InFunTL (instantiate0 b) : stk) (instantiate0 a)
rec petrol bci denv stk (In (ConT qc [])) =
  ret (petrol - 1) bci denv stk (In (ConT qc []))
rec petrol bci denv stk (In (ConT qc (a:as))) =
  rec (petrol - 1) bci denv (InConT qc [] (map instantiate0 as) : stk) (instantiate0 a)
rec petrol bci denv stk (In (CompT a)) =
  rec (petrol - 1) bci denv (InCompT : stk) (instantiate0 a)
rec petrol bci denv stk (In (ForallT k sc)) =
  ret (petrol - 1) bci denv stk (In (ForallT k sc))
rec petrol bci denv stk (In ByteStringT) =
  ret (petrol - 1) bci denv stk (In ByteStringT)
rec petrol bci denv stk (In IntegerT) =
  ret (petrol - 1) bci denv stk (In IntegerT)
rec petrol bci denv stk (In FloatT) =
  ret (petrol - 1) bci denv stk (In FloatT)
rec petrol bci denv stk (In (LamT k sc)) =
  ret (petrol - 1) bci denv stk (In (LamT k sc))
rec petrol bci denv stk (In (AppT f a)) =
  rec (petrol - 1) bci denv (InAppTL (instantiate0 a) : stk) (instantiate0 f)





ret :: Petrol -> BlockChainInfo -> QualifiedEnv -> CKStack -> Term -> Either String Term
ret 0 _ _ _ _ = Left "Out of petrol."
ret _ _ _ [] tm = Right tm
ret petrol bci denv (InIsaL a : stk) m' =
  rec (petrol - 1) bci denv (InIsaR m' : stk) a
ret petrol bci denv (InIsaR m' : stk) a' =
  ret (petrol - 1) bci denv stk (isaH m' a')
ret petrol bci denv (InAbst : stk) m =
  ret (petrol - 1) bci denv stk m
ret petrol bci denv (InInstL a : stk) m' =
  rec (petrol - 1) bci denv (InInstR m' : stk) a
ret petrol bci denv (InInstR m' : stk) a' =
  ret (petrol - 1) bci denv stk (instH m' a')
ret petrol bci denv (InAppLeft x : stk) f =
  rec (petrol - 1) bci denv (InAppRight f : stk) x
ret petrol bci denv (InAppRight f : stk) x =
  case f of
    In (Lam sc) ->
      rec (petrol - 1) bci denv stk (instantiate sc [x])
    _ ->
      ret (petrol - 1) bci denv stk (appH f x)
ret petrol bci denv (InCon c revls rs : stk) m =
  case rs of
    [] -> ret (petrol - 1) bci denv stk (conH c (reverse (m:revls)))
    m':rs' -> rec (petrol - 1) bci denv (InCon c (m:revls) rs' : stk) m'
ret petrol bci denv (InCase cs : stk) m =
  case matchClauses cs m of
    Nothing ->
      Left ("Incomplete pattern match: "
             ++ pretty (In (Case (scope [] m) cs)))
    Just m'  ->
      rec (petrol - 1) bci denv stk m'
ret petrol bci denv (InSuccess : stk) m =
  ret (petrol - 1) bci denv stk (successH m)
ret petrol bci denv (InBind sc : stk) m =
  case m of
    In Failure ->
      ret (petrol - 1) bci denv stk failureH
    In (Success m') ->
      rec (petrol - 1) bci denv stk (instantiate sc [instantiate0 m'])
    _ ->
      Left ("Cannot bind a non-computation: " ++ pretty m)
ret petrol bci denv (InBuiltin n revls rs : stk) m =
  case rs of
    [] -> case builtin n (reverse (m:revls)) of
      Left err ->
        Left err
      Right m' ->
        ret (petrol - 1) bci denv stk m'
    m':rs' ->
      rec (petrol - 1) bci denv (InBuiltin n (m:revls) rs' : stk) m'
ret petrol bci denv (InFunTL b : stk) a' =
  rec (petrol - 1) bci denv (InFunTR a' : stk) b
ret petrol bci denv (InFunTR a' : stk) b' =
  ret (petrol - 1) bci denv stk (funTH a' b')
ret petrol bci denv (InConT qc revas' [] : stk) a' =
  ret (petrol - 1) bci denv stk (conTH qc (reverse (a':revas')))
ret petrol bci denv (InConT qc revas' (a2:as) : stk) a' =
  rec (petrol - 1) bci denv (InConT qc (a':revas') as : stk) a2
ret petrol bci denv (InCompT : stk) a' = 
  ret (petrol - 1) bci denv stk (compTH a')
ret petrol bci denv (InAppTL a : stk) f' =
  rec (petrol - 1) bci denv (InAppTR f' : stk) a
ret petrol bci denv (InAppTR f' : stk) a' =
  ret (petrol - 1) bci denv stk (appTH f' a')




evaluate :: BlockChainInfo -> QualifiedEnv -> Petrol -> Term -> Either String Term
evaluate bci denv ptrl tm = rec ptrl bci denv [] tm