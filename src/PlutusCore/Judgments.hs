{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}







module PlutusCore.Judgments where

-- import Utils.ABT
-- import qualified Utils.ProofDeveloper as PD
import PlutusCore.Contexts
import PlutusCore.Program
import PlutusCore.Term







data Judgment r where
  
  -- Θ ⊢ A :: K
  IsTypeJ :: Context
          -> Term
          -> Judgment Kind
  
  -- A tyval
  IsTypeValueJ :: Term
               -> Judgment ()
  
  -- M val
  IsTermValueJ :: Term
               -> Judgment ()
  
  -- Θ ⊢ A ∋ M
  CheckJ :: Context
         -> Term
         -> Term
         -> Judgment ()
  
  -- Θ ⊢ M ∈ A
  SynthJ :: Context
         -> Term
         -> Judgment Term
  
  -- Θ ; κ A* ⊢ C ∋ cl
  ClauseJ :: Context
          -> String
          -> [Type]
          -> Type
          -> Clause
          -> Judgment ()
  
  -- Θ ⊢ A = B
  EqualJ :: Context
         -> Type
         -> Type
         -> Judgment ()
  
  -- Θ ⊢ A* = B*
  EqualAllJ :: Context
            -> Term
            -> [Term]
            -> Judgment ()
  
  -- Δ ⊢ P program
  ElabProgramJ :: Program
               -> Judgment ()
  
  -- Δ ⊢ D decl
  ElabDeclJ :: NominalContext
            -> Declaration
            -> Judgment ()
  
  -- Δ ⊢ a alt (α* K*)
  ElabAltJ :: NominalContext
           -> Alt
           -> [KindSig]
           -> Judgment ()