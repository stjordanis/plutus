{-# OPTIONS -Wall #-}







module PlutusCore.Contexts where

import PlutusCore.Program
import PlutusCore.Term






type NominalContext = ([Module], [Declaration])



data HypotheticalJudgment = HasKind String Kind
                          | HasType String Term

variableName :: HypotheticalJudgment -> String
variableName (HasKind n _) = n
variableName (HasType n _) = n


type HypotheticalContext = [HypotheticalJudgment]



data Context = Context
               { currentModule :: String
               , moduleImports :: [String]
               , nominalContext :: NominalContext
               , hypotheticalContext :: HypotheticalContext
               }

extendNomMod :: Context -> Module -> Context
extendNomMod ctx l =
  ctx { nominalContext = (l:ls, ds) }
  where (ls,ds) = nominalContext ctx

extendNomDecl  :: Context -> Declaration -> Context
extendNomDecl ctx d =
  ctx { nominalContext = (ls, d:ds) }
  where (ls,ds) = nominalContext ctx

extendHyp :: Context -> [HypotheticalJudgment] -> Context
extendHyp ctx hjs = ctx { hypotheticalContext =
                            hjs ++ hypotheticalContext ctx
                        }