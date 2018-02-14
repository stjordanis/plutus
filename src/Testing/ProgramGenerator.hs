{-# OPTIONS -Wall #-}
{-# LANGUAGE OverloadedStrings #-}







module Testing.ProgramGenerator where

import Control.Applicative                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     
import Control.Monad.State
import qualified Data.ByteString.Lazy as BS

import PlutusShared.Qualified
import PlutusCore.Contexts
import PlutusCore.Term

import Utils.ABT
import Utils.Pretty
import Utils.Vars








data BackgroundContext = BackgroundContext
                         { currentModule :: String
                         , knownModules :: [String]
                         , nominalContext :: NominalContext
                         }

data RightSearchableType = RSTVar String
                         | RSTConT QualifiedConstructor [Type]

data RightSearchableJudgment = RSJHasType String RightSearchableType
                             | RSJHasKind String Kind

data LeftSearchableType = LSTVar String
                        | LSTFunT Type Type
                        | LSTForallT Kind (Scope TermF)
                        | LSTCompT Type

data LeftSearchableJudgment = LSJHasType String LeftSearchableType
                            | LSJHasKind String Kind

type LeftSearchableContext = [LeftSearchableJudgment]





findVar :: LeftSearchableContext -> String -> [String]
findVar [] _ = []
findVar (LSJHasType x (LSTVar a') : ctx) a | a == a' = x : findVar ctx a
findVar (_ : ctx) a = findVar ctx a



newName :: StateT Int [] String
newName = do i <- get
             put (i+1)
             return ("x" ++ show i)

invertR :: Int -> BackgroundContext -> LeftSearchableContext -> HypotheticalContext -> Type -> StateT Int [] Term
invertR 0 _ _ _ _ = lift []
invertR n gth gg go (Var (Free (FreeVar a))) =
  lift $ map (Var . Free . FreeVar) (findVar gg a)
invertR _ _   _  _  (Var _) = lift []
invertR n gth gg go (In (DecnameT v)) = lift []
invertR n gth gg go (In (FunT s t)) =
  do x <- newName
     m <- invertR (n - 1) gth gg (HasType x (instantiate0 s) : go)
                  (instantiate0 t)
     return $ lamH x m
invertR n gth gg go (In (ConT k ts)) = _
invertR n gth gg go (In (CompT t)) =
  return failureH <|>
    do m <- invertR (n - 1) gth gg go (instantiate0 t)
       return $ successH m
invertR n gth gg go (In (ForallT k sc)) =
  do a <- newName
     m <- invertR (n - 1) gth gg (HasKind a k : go) (instantiate sc [Var (Free (FreeVar a))])
     return $ abstH a m
invertR n gth gg go (In IntegerT) =
  lift $ map primIntegerH [0..10]
invertR n gth gg go (In FloatT) =
  lift $ map primFloatH [0..10]
invertR n gth gg go (In ByteStringT) =
  lift [ primByteStringH "foobarbaz"
       , primByteStringH "quuxdoogarply"
       ]
invertR n gth gg go (In (LamT _ _)) = lift []
invertR n gth gg go (In (AppT _ _)) = lift []
invertR _ _   _  _  m = error ("Cannot invert on non-type " ++ pretty m)

{-

invertR : ℕ → (Θ : BackgroundContext) → (Γ : Ctx LeftSearchableHypJ) (Ω : Ctx HypJ) (T : Type) → List (Σ Term λ M → Θ , Γ , Ω ⟶R M ∶ T)
  invertR zero Θ Γ Ω T = []
  invertR (suc n) Θ Γ Ω (var (sorted _ α)) with findVar Γ α
  ... | yes ps = Data.List.map (\ { (pr x v) -> pr (var (sorted tm x)) (init-var v) }) (list1ToList ps)
  ... | no ¬v = Data.List.map (\ { (pr M p) -> pr M (LR-P ¬v p) }) (invertL n Θ Γ Ω (var α))
  invertR (suc n) Θ Γ Ω (nameT ν^) = []
  invertR (suc n) Θ Γ Ω (funT S T) =
    for (invertR n Θ Γ (Ω , x ∶ S) T) λ {
      (pr M p) → pr (lam x M) (lam p)
    }
    where x = freshVar Γ Ω S
  invertR (suc n) Θ Γ Ω PreludeT κ^ T*) with constructorType Θ κ^
  invertR (suc n) Θ Γ Ω PreludeT κ^ T*) | invalid x = []
  invertR (suc n) Θ Γ Ω PreludeT κ^ T*) | noConstructor x =
    for (invertL n Θ Γ Ω PreludeT κ^ T*)) λ {
      (pr M p) → pr M (LR-no-constructor-con x p)
    }
  invertR (suc n) Θ Γ Ω PreludeT κ^ T*) | singleConstructor (pr c^ p) sig =
    for foundArgs λ {
      argMs → pr Prelude c^ (for argMs λ { (pr _ (pr M _)) → M }))
                 (single-constructor-con {!!} {!!} {!!})
    }
    where
      args = constructorArguments T* sig
      foundArgs : List (List (Σ Type λ S → Σ Term λ M → Θ , Γ , Ω ⟶R M ∶ S))
      foundArgs = sequenceList (for args λ S → for (invertR n Θ Γ Ω S) λ { (pr M p) → pr S (pr M p) })
      -- aux : (Ms : List (Σ Type λ S → Σ Term λ M → Θ , Γ , Ω ⟶R M ∶ S)) → (i : ℕ) → (p : i ≤ length Ms) → (p' : i ≤ 
  invertR (suc n) Θ Γ Ω PreludeT κ^ T*) | multipleConstructor x cs =
    for (invertL n Θ Γ Ω PreludeT κ^ T*)) λ {
      (pr M p) → pr M (LR-multiple-constructor-con x p)
    }
  invertR (suc n) Θ Γ Ω (compT T) =
    cons (pr failure failure)
         (for (invertR n Θ Γ Ω T) λ {
           (pr M p) → pr (success M) (success p)
         })
  invertR (suc n) Θ Γ Ω (forallT α K T) =
    for (invertR n Θ Γ (Ω , α ∷ K) T) λ {
      (pr M p) → pr (abs α M) (abs p)
    }
  invertR (suc n) Θ Γ Ω integerT = cons (pr (integer intlit) int) []
  invertR (suc n) Θ Γ Ω floatT = cons (pr (float floatlit) float) []
  invertR (suc n) Θ Γ Ω bytestringT = cons (pr (bytestring bytestringlit) bytestring) []
  invertR (suc n) Θ Γ Ω (lamT α K T) = []
  invertR (suc n) Θ Γ Ω (appT S T) = []

-}


invertL :: Int -> BackgroundContext -> LeftSearchableContext -> HypotheticalContext -> RightSearchableType -> StateT Int [] Term
invertL 0 _ _ _ _ = lift []
invertL n gth gg [] (RSTVar x) = lift []
invertL n gth gg [] (RSTConT qc as) = _
invertL n gth gg (HasKind a k : go) t =
  invertL (n - 1) gth (LSJHasKind a k : gg) go t
invertL _ _   _ (HasType _ (Var (Bound _ _)) : _) _ = lift []
invertL _ _   _ (HasType _ (Var (Meta _)) : _) _ = lift []
invertL n gth gg (HasType x (Var (Free (FreeVar a))) : go) t@(RSTVar a')
  | a == a' = return (Var (Free (FreeVar x))) <|> invertL n gth gg go t
  | otherwise = invertL n gth gg go t
invertL n gth gg (HasType x (Var (Free (FreeVar a))) : go) t@(RSTConT _ _) =
  invertL (n - 1) gth (LSJHasType x (LSTVar a) : gg) go t
invertL _ _   _  (HasType _ (In (DecnameT _)) : _) _ =
  lift []
invertL n gth gg (HasType x (In (FunT a b)) : go) t =
  invertL (n - 1) gth (LSJHasType x (LSTFunT (instantiate0 a) (instantiate0 b)) : gg) go t
invertL n gth gg (HasType x (In (ConT kappaa as)) : go) t =
  _
invertL n gth gg (HasType x (In (CompT a)) : go) t =
  invertL (n - 1) gth (LSJHasType x (LSTCompT (instantiate0 a)) : gg) go t
invertL n gth gg (HasType x (In (ForallT k sc)) : go) t =
  invertL (n - 1) gth (LSJHasType x (LSTForallT k sc) : gg) go t
invertL n gth gg (HasType x (In IntegerT) : go) t =
  invertL (n - 1) gth gg go t
invertL n gth gg (HasType x (In FloatT) : go) t =
  invertL (n - 1) gth gg go t
invertL n gth gg (HasType x (In ByteStringT) : go) t =
  invertL (n - 1) gth gg go t
invertL n gth gg (HasType x (In y) : go) t =
  lift []

{-

  invertL : ℕ → (Θ : BackgroundContext) → (Γ : Ctx LeftSearchableHypJ) (Ω : Ctx HypJ) (T : RightSearchableType) → List (Σ Term λ M → Θ , Γ , Ω ⟶L M ∶ T)
  invertL zero Θ Γ Ω T = []
  invertL (suc n) Θ Γ <> (var α) = []
  invertL (suc n) Θ Γ <> PreludeT κ^ T*) =
    -- search if multi-constructor, search Γ if zero-constructor, fail otherwise
    {!!}
  invertL (suc n) Θ Γ (Ω , α ∷ K) T =
    for (invertL n Θ (Γ , α ∷ K) Ω T) λ {
      (pr M p) → pr M (kind p)
    }
    
    
  invertL (suc n) Θ Γ (Ω , x ∶ var (sorted _ α)) (var α') with α ≟ α'
  
  invertL (suc n) Θ Γ (Ω , x ∶ var (sorted _ α)) (var .α) | yes refl =
    cons (pr (var (sorted tm x)) init-var)
        (for (invertL n Θ (Γ , x ∶ var α) Ω (var α)) λ { (pr M p) → pr M (var-shift p) })
  
  invertL (suc n) Θ Γ (Ω , x ∶ var (sorted _ α)) (var α') | no ¬p =
    for (invertL n Θ (Γ , x ∶ var α) Ω (var α')) λ { (pr M p) → pr M (var-shift p) }
  
  
  invertL (suc n) Θ Γ (Ω , x ∶ var (sorted _ α)) PreludeT κ^ T*) =
    for (invertL n Θ (Γ , x ∶ var α) Ω PreludeT κ^ T*)) λ {
      (pr M p) → pr M (var-shift p)
    }
    
    
    
    
  invertL (suc n) Θ Γ (Ω , x ∶ nameT ν^) T = []
  invertL (suc n) Θ Γ (Ω , x ∶ funT R S) T =
    for (invertL n Θ (Γ , x ∶ funT R S) Ω T) λ {
      (pr M p) → pr M (funT p)
    }
  invertL (suc n) Θ Γ (Ω , x ∶ conT κ^ S*) T =
    -- do case
    {!!}
  invertL (suc n) Θ Γ (Ω , x ∶ compT S) T =
    for (invertL n Θ (Γ , x ∶ compT S) Ω T) λ {
      (pr M p) → pr M (compT p)
    }
  invertL (suc n) Θ Γ (Ω , x ∶ forallT α K S) T =
    for (invertL n Θ (Γ , x ∶ forallT α K S) Ω T) λ {
      (pr M p) → pr M (forallT p)
    }
  invertL (suc n) Θ Γ (Ω , x ∶ integerT) T =
    for (invertL n Θ Γ Ω T) λ {
      (pr M p) → pr M (integerT p)
    }
  invertL (suc n) Θ Γ (Ω , x ∶ floatT) T =
    for (invertL n Θ Γ Ω T) λ {
      (pr M p) → pr M (floatT p)
    }
  invertL (suc n) Θ Γ (Ω , x ∶ bytestringT) T =
    for (invertL n Θ Γ Ω T) λ {
      (pr M p) → pr M (bytestringT p)
    }
  invertL (suc n) Θ Γ (Ω , x ∶ lamT α K S) T = []
  invertL (suc n) Θ Γ (Ω , x ∶ appT R S) T = []

-}