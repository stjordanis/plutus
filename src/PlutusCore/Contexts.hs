{-# OPTIONS -Wall #-}







module PlutusCore.Contexts where

import PlutusCore.Program
import PlutusCore.Term






type NominalContext = [Declaration]



data HypotheticalJudgment = HasKind String Kind
                          | HasType String Term

variableName :: HypotheticalJudgment -> String
variableName (HasKind n _) = n
variableName (HasType n _) = n


type HypotheticalContext = [HypotheticalJudgment]



data Context = Context
               { nominalContext :: NominalContext
               , hypotheticalContext :: HypotheticalContext
               }

extendNomDecl  :: Context -> Declaration -> Context
extendNomDecl ctx d =
  ctx { nominalContext = d : nominalContext ctx }

extendHyp :: Context -> [HypotheticalJudgment] -> Context
extendHyp ctx hjs = ctx { hypotheticalContext =
                            hjs ++ hypotheticalContext ctx
                        }