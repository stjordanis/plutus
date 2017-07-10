{-# OPTIONS -Wall #-}







module PlutusShared.BoolToTerm where

import PlutusCore.Term
import PlutusShared.Qualified







boolToTerm :: Bool -> Term
boolToTerm True = conH (QualifiedConstructor "Prim" "True") []
boolToTerm False = conH (QualifiedConstructor "Prim" "False") []