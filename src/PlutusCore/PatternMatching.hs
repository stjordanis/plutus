{-# OPTIONS -Wall #-}







module PlutusCore.PatternMatching where

import PlutusCore.Term
import PlutusShared.Qualified
import Utils.ABT

-- import Control.Monad







matchPattern :: QualifiedConstructor -> Int -> Term -> Maybe [Term]
matchPattern c l (In (Con c' as))
  | c == c' && l == length as =
    Just (map instantiate0 as)
matchPattern _ _ _ = Nothing

matchClauses :: [Clause] -> Term -> Maybe Term
matchClauses [] _ =
  Nothing
matchClauses (Clause c sc:cs) v =
  case matchPattern c (length (names sc)) v of
    Nothing -> matchClauses cs v
    Just xs -> Just (instantiate sc xs)