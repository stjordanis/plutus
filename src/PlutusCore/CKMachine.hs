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







data CKFrame = InLet (Scope TermF)
             | InAppLeft Term
             | InAppRight Term
             | InCon QualifiedConstructor [Term] [Term]
             | InCase [ClauseF (Scope TermF)]
             | InSuccess
             | InBind (Scope TermF)
             | InBuiltin String [Term] [Term]
             | InIsFun
             | InIsCon
             | InIsConName QualifiedConstructor
             | InIsInt
             | InIsFloat
             | InIsByteString

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
  Right (Var x)
rec petrol bci denv stk (In (Decname n)) =
  case lookup n denv of
    Nothing ->
      Left ("Unknown constant/defined term: " ++ prettyQualifiedName n)
    Just m ->
      ret (petrol - 1) bci denv stk m
rec petrol bci denv stk (In (Let m sc)) =
  rec (petrol - 1) bci denv (InLet sc : stk) (instantiate0 m)
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
rec petrol bci denv stk (In (IsFun m)) =
  rec (petrol -1) bci denv (InIsFun : stk) (instantiate0 m)
rec petrol bci denv stk (In (IsCon m)) =
  rec (petrol -1) bci denv (InIsCon : stk) (instantiate0 m)
rec petrol bci denv stk (In (IsConName qc m)) =
  rec (petrol -1) bci denv (InIsConName qc : stk) (instantiate0 m)
rec petrol bci denv stk (In (IsInt m)) =
  rec (petrol -1) bci denv (InIsInt : stk) (instantiate0 m)
rec petrol bci denv stk (In (IsFloat m)) =
  rec (petrol -1) bci denv (InIsFloat : stk) (instantiate0 m)
rec petrol bci denv stk (In (IsByteString m)) =
  rec (petrol -1) bci denv (InIsByteString : stk) (instantiate0 m)





ret :: Petrol -> BlockChainInfo -> QualifiedEnv -> CKStack -> Term -> Either String Term
ret 0 _ _ _ _ = Left "Out of petrol."
ret _ _ _ [] tm = Right tm
ret petrol bci denv (InLet sc : stk) m =
  rec (petrol - 1) bci denv stk (instantiate sc [m])
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
ret petrol bci denv (InIsFun : stk) m =
  case m of
    In (Lam _) -> ret (petrol - 1) bci denv stk (boolToTerm True)
    _ -> ret (petrol - 1) bci denv stk (boolToTerm False)
ret petrol bci denv (InIsCon : stk) m =
  case m of
    In (Con _ _) -> ret (petrol - 1) bci denv stk (boolToTerm True)
    _ -> ret (petrol - 1) bci denv stk (boolToTerm False)
ret petrol bci denv (InIsConName qc : stk) m =
  case m of
    In (Con qc' _) | qc == qc' ->
      ret (petrol - 1) bci denv stk (boolToTerm True)
    _ -> ret (petrol - 1) bci denv stk (boolToTerm False)
ret petrol bci denv (InIsInt : stk) m =
  case m of
    In (PrimInt _) -> ret (petrol - 1) bci denv stk (boolToTerm True)
    _ -> ret (petrol - 1) bci denv stk (boolToTerm False)
ret petrol bci denv (InIsFloat : stk) m =
  case m of
    In (PrimFloat _) -> ret (petrol - 1) bci denv stk (boolToTerm True)
    _ -> ret (petrol - 1) bci denv stk (boolToTerm False)
ret petrol bci denv (InIsByteString : stk) m =
  case m of
    In (PrimByteString _) -> ret (petrol - 1) bci denv stk (boolToTerm True)
    _ -> ret (petrol - 1) bci denv stk (boolToTerm False)




evaluate :: BlockChainInfo -> QualifiedEnv -> Petrol -> Term -> Either String Term
evaluate bci denv ptrl tm = rec ptrl bci denv [] tm