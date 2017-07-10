{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveGeneric #-}







module PlutusShared.Qualified where

import Utils.JSABT

import GHC.Generics







data QualifiedName = QualifiedName String String
  deriving (Eq,Generic)

prettyQualifiedName :: QualifiedName -> String
prettyQualifiedName (QualifiedName l n) =
  "(qual " ++ l ++ " " ++ n ++ ")"

instance ToJS QualifiedName where
  toJS (QualifiedName l n) =
    JSABT "QualifiedName"
          [JSString l, JSString n]



data QualifiedConstructor = QualifiedConstructor String String
  deriving (Eq,Generic)

prettyQualifiedConstructor :: QualifiedConstructor -> String
prettyQualifiedConstructor (QualifiedConstructor l c) =
  "(qualcon " ++ l ++ " " ++ c ++ ")"

instance ToJS QualifiedConstructor where
  toJS (QualifiedConstructor l c) =
    JSABT "QualifiedConstructor"
          [JSString l, JSString c]