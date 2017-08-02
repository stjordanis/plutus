{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS -Wall #-}





-- | This module defines what it means to be a program in Plutus Core.

module PlutusCore.Program where

import Utils.Pretty
import Utils.Names
import PlutusCore.Term

import Data.List (intercalate)

import GHC.Generics







data KindSig = KindSig String Kind

prettyKindSig :: KindSig -> String
prettyKindSig (KindSig x k) =
  "("
    ++ x
    ++ " "
    ++ prettyKind k
    ++ ")"

data Alt = Alt String [Term]

prettyAlt :: Alt -> String
prettyAlt (Alt c ts) =
  "("
    ++ c
    ++ " "
    ++ unwords (map (parenthesize Nothing) ts)
    ++ ")"


data Declaration = DataDeclaration String [KindSig] [Alt]
                 | TypeDeclaration String Term
                 | TermDeclaration String Term
                 | TermDefinition String Term

prettyDeclaration :: Declaration -> String
prettyDeclaration (DataDeclaration c ks alts) =
  "(data "
    ++ c
    ++ " "
      ++ "("
      ++ unwords (map prettyKindSig ks)
      ++ ")"
    ++ " "
    ++ unwords (map prettyAlt alts)
    ++ ")"
prettyDeclaration (TypeDeclaration n tv) =
  "(type "
    ++ n
    ++ " "
    ++ parenthesize Nothing tv
    ++ ")"
prettyDeclaration (TermDeclaration n t) =
  "(declare "
    ++ n
    ++ " "
    ++ parenthesize Nothing t
    ++ ")"
prettyDeclaration (TermDefinition n v) =
  "(define "
    ++ n
    ++ " "
    ++ parenthesize Nothing v
    ++ ")"



type Imports = [String]

data TypeExport = TypeNameExport String
                | TypeConstructorExport String [String]

data Exports = Exports [TypeExport] [String]





-- | A `Module` is a named collection of declarations.

data Module = Module String Imports Exports [Declaration]

prettyModule :: Module -> String
prettyModule (Module l impd expd decls) =
  "(module "
    ++ l
    ++ " "
    ++ prettyImports impd
    ++ " "
    ++ prettyExports expd
    ++ " "
    ++ unwords (map prettyDeclaration decls)
    ++ ")"
  where
    prettyImports ls =
      "(imported "
        ++ unwords ls
        ++ ")"
    prettyExports (Exports typeExports names) =
      "(exported "
          ++ "("
          ++ unwords (map prettyExport typeExports)
          ++ ")"
        ++ " "
          ++ "("
          ++ unwords names
          ++ ")"
        ++ ")"
    prettyExport (TypeNameExport n) = n
    prettyExport (TypeConstructorExport c cs) =
      "("
        ++ c
        ++ " "
          ++ "("
          ++ unwords cs
          ++ ")"
        ++ ")"





-- | A `Program` is a collection of modules.

data Program =
  Program [Module]

prettyProgram :: Program -> String
prettyProgram (Program mods) =
  "(program " ++ unwords (map prettyModule mods) ++ ")"