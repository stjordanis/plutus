{-# OPTIONS -Wall #-}







module PlutusCore.PatternMatching where

import PlutusCore.Term
import Utils.ABTs.ABT

-- import Control.Monad







matchPattern :: String -> Int -> Term -> Maybe [Term]
matchPattern c l (Con c' :$: as)
  | c == c' && l == length as =
    Just (map instantiate0 as)
matchPattern _ _ _ = Nothing

matchClauses :: [Clause] -> Term -> Maybe Term
matchClauses [] _ =
  Nothing
matchClauses ((Clause c :$: [sc]):cs) v =
  case matchPattern c (length (names sc)) v of
    Nothing -> matchClauses cs v
    Just xs -> Just (instantiate sc xs)
matchClauses _ _ =
    error "You attempted to match on a syntactically malformed clause. There \
          \should be no way to reach this clause."