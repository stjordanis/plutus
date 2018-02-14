{-# OPTIONS -Wall #-}







module PlutusShared.BoolToTerm where

import PlutusCore.Term

import Utils.ABT
import Utils.Vars







boolToTerm :: Bool -> Term
boolToTerm True = conH "True" []
boolToTerm False = conH "False" []



boolToScottTerm :: Bool -> Term
boolToScottTerm True = abstH "r" (lamH "t" (lamH "f" (appH (Var (Free (FreeVar "t"))) (abstH "a" (lamH "x" (Var (Free (FreeVar "x"))))))))
boolToScottTerm False = abstH "r" (lamH "t" (lamH "f" (appH (Var (Free (FreeVar "f"))) (abstH "a" (lamH "x" (Var (Free (FreeVar "x"))))))))