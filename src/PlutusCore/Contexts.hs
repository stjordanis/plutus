{-# OPTIONS -Wall #-}







module PlutusCore.Contexts where

import Utils.ABT
import PlutusCore.Term






data NominalJudgment = ModJ String
                     | ExpTypeJ String String
                     | ExpTermJ String String
                     | TermJ String String Term
                     | DefJ String String Term
                     | ConJ String String [Scope TermF] String
                     | TyConJ String String [Kind]
                     | TypeJ String String Term Kind

type NominalContext = [NominalJudgment]



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

extendNom :: Context -> [NominalJudgment] -> Context
extendNom ctx njs = ctx { nominalContext =
                            njs ++ nominalContext ctx
                        }

extendHyp :: Context -> [HypotheticalJudgment] -> Context
extendHyp ctx hjs = ctx { hypotheticalContext =
                            hjs ++ hypotheticalContext ctx
                        }