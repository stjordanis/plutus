{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}







module PlutusCore.Judgments where

-- import Utils.ABT
-- import qualified Utils.ProofDeveloper as PD
import PlutusCore.Contexts
import PlutusCore.Program
import PlutusCore.Term
import PlutusShared.Qualified







data Judgment r where
  IsTypeJ :: Context -> Term -> Judgment Kind
  IsTypeValueJ :: Term -> Judgment ()
  IsTermValueJ :: Term -> Judgment ()
  CheckJ :: Context -> Term -> Term -> Judgment ()
  SynthJ :: Context -> Term -> Judgment Term
  ClauseJ :: Context
          -> QualifiedConstructor
          -> [Term]
          -> Term
          -> Clause
          -> Judgment ()
  EqualJ :: Context -> Term -> Term -> Judgment ()
  EqualAllJ :: Context -> Term -> [Term] -> Judgment ()
  ElabProgramJ :: Program -> Judgment ()
  ElabModuleJ :: [Module] -> Module -> Judgment ()
  ElabDeclJ :: String
            -> [String]
            -> NominalContext
            -> Declaration
            -> Judgment ()
  ElabAltJ :: String
           -> [String]
           -> NominalContext
           -> Alt
           -> [KindSig]
           -> Judgment ()