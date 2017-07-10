{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS -Wall #-}





-- | This module defines what it means to be a program in Plutus Core.

module PlutusCore.Program where

import Utils.Pretty
import Utils.Names
import PlutusCore.Term

import Data.List (intercalate)

import GHC.Generics







-- | A `Declaration` can declare exported and local terms, and also exported
-- and local constructors.

data Declaration = Export String Term
                 | Local String Term
                 | ExportConstructor String
                 | LocalConstructor String

prettyDeclaration :: Declaration -> String
prettyDeclaration (Export n m) =
  "(exp " ++ n ++ " " ++ pretty m ++ ")"
prettyDeclaration (Local n m) =
  "(loc " ++ n ++ " " ++ pretty m ++ ")"
prettyDeclaration (ExportConstructor c) =
  "(expcon " ++ c ++ ")"
prettyDeclaration (LocalConstructor c) =
  "(loccon " ++ c ++ ")"





-- | A `Module` is a named collection of declarations.

data Module = Module String [Declaration]

prettyModule :: Module -> String
prettyModule (Module l decls) =
  "(module " ++ l ++ " " ++ unwords (map prettyDeclaration decls) ++ ")"





-- | A `Program` is a collection of modules.

data Program =
  Program [Module]

prettyProgram :: Program -> String
prettyProgram (Program mods) =
  "(program " ++ unwords (map prettyModule mods) ++ ")"