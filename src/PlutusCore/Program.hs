{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS -Wall #-}





-- | This module defines what it means to be a program in Plutus Core.

module PlutusCore.Program where

import Utils.ABT
import Utils.Pretty
import PlutusShared.Qualified
import PlutusCore.Term

import Data.List (isPrefixOf)

-- import GHC.Generics







data KindSig = KindSig String Kind

prettyKindSig :: KindSig -> String
prettyKindSig (KindSig x k) =
  "("
    ++ x
    ++ " "
    ++ prettyKind k
    ++ ")"

data Alt = Alt String [Scope PlutusSig]

prettyAlt :: Alt -> String
prettyAlt (Alt c tscs) =
  "("
    ++ c
    ++ " "
    ++ unwords (map (parenthesize Nothing . body) tscs)
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
prettyDeclaration (TermDeclaration n tv) =
  "(define "
    ++ n
    ++ " "
    ++ parenthesize Nothing tv
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
    prettyExports (Exports typeExports termExports) =
      "(exported "
          ++ "("
          ++ unwords (map prettyExport typeExports)
          ++ ")"
        ++ " "
          ++ "("
          ++ unwords termExports
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



firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Nothing:xs) = firstJust xs
firstJust (Just x:_) = Just x

typeForQualifiedName :: Program -> QualifiedName -> Maybe Type
typeForQualifiedName (Program ls) (QualifiedName l n) =
  firstJust (map typeForQualifiedNameModule ls)
  where
    typeForQualifiedNameModule :: Module -> Maybe Type
    typeForQualifiedNameModule (Module l' _ _ decls) | l == l' =
      firstJust (map typeForQualifiedNameDecl decls)
    typeForQualifiedNameModule _ = Nothing
    
    typeForQualifiedNameDecl :: Declaration -> Maybe Type
    typeForQualifiedNameDecl (TermDeclaration n' t) | n == n' = Just t
    typeForQualifiedNameDecl _ = Nothing




definitionForQualifiedName :: Program -> QualifiedName -> Maybe Type
definitionForQualifiedName (Program ls) (QualifiedName l n) =
  firstJust (map definitionForQualifiedNameModule ls)
  where
    definitionForQualifiedNameModule :: Module -> Maybe Type
    definitionForQualifiedNameModule (Module l' _ _ decls) | l == l' =
      firstJust (map definitionForQualifiedNameDecl decls)
    definitionForQualifiedNameModule _ = Nothing

    definitionForQualifiedNameDecl :: Declaration -> Maybe Type
    definitionForQualifiedNameDecl (TermDefinition n' m) | n == n' = Just m
    definitionForQualifiedNameDecl _ = Nothing




namesWithQualifiedNameAsPrefix :: Program -> QualifiedName -> [QualifiedName]
namesWithQualifiedNameAsPrefix (Program ls) (QualifiedName l n) =
  ls >>= namesWithQualifiedNameAsPrefixModule
  where
    namesWithQualifiedNameAsPrefixModule :: Module -> [QualifiedName]
    namesWithQualifiedNameAsPrefixModule (Module l' _ _ decls) | l == l' =
      decls >>= namesWithQualifiedNameAsPrefixDecl
    namesWithQualifiedNameAsPrefixModule _ = []

    namesWithQualifiedNameAsPrefixDecl :: Declaration -> [QualifiedName]
    namesWithQualifiedNameAsPrefixDecl (TermDefinition n' m)
      | isPrefixOf n n' = [QualifiedName l n']
    namesWithQualifiedNameAsPrefixDecl _ = []