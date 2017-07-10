{-# OPTIONS -Wall #-}







-- | This module defines the representations of the various kinds of contexts
-- that the Plutus Core scope checker requires.

module ScopeChecking.Contexts where







-- | A `VariableContext` consists of just a collection of variable names.

type VariableContext = [String]





-- | A `ModuleContext` consists of just a collection of module names.

type ModuleContext = [String]





-- | A `NominalJudgment` is either an export or local judgment, consisting
-- of a module name and a declared name.

data NominalJudgment = Exp String String | Loc String String



-- | A `NominalContext` consists of a collection of nominal judgments.

type NominalContext = [NominalJudgment]