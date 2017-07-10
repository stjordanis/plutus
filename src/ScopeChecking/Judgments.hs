{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}







-- | This module defines the various hypothetical judgments that are required
-- for scope checking of Plutus Core.

module ScopeChecking.Judgments where

import PlutusCore.Program
import PlutusCore.Term
import PlutusShared.Qualified
import ScopeChecking.Contexts







-- | A `Judgement` is the top-level kind of judgment used for scope checking
-- of Plutus Core.

data Judgment r where
  
  -- Δ ; Γ ⊢ M term l
  TermInModule :: NominalContext
               -> VariableContext
               -> Term
               -> String
               -> Judgment ()
  
  -- Δ permits qn in l
  Permits :: NominalContext
          -> QualifiedName
          -> String
          -> Judgment ()
  
  -- Δ permits constructor qc in l
  PermitsConstructor :: NominalContext
                     -> QualifiedConstructor
                     -> String
                     -> Judgment ()
  
  -- Δ ; Γ ⊢ C clause l
  Clause :: NominalContext
         -> VariableContext
         -> Clause
         -> String
         -> Judgment ()
  
  -- Δ ⊢ D decl l ⊣ Δ'
  Decl :: NominalContext
       -> Declaration
       -> String
       -> Judgment NominalContext
  
  -- Λ ; Δ ⊢ L module ⊣ Λ' ; Δ'
  Mod :: ModuleContext
      -> NominalContext
      -> Module
      -> Judgment (ModuleContext,NominalContext)
  
  -- Δ ⊢ G program ⊣ Δ'
  Prog :: NominalContext
       -> Program
       -> Judgment NominalContext