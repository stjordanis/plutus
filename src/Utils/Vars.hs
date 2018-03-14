{-# OPTIONS -Wall #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}







module Utils.Vars where





import GHC.Generics





-- * Variable types



-- | Three types of variables are used. 'Free' variables are for
-- user-supplied names that can be abstracted for binding, or can be left
-- free for use as names for defined terms, and other such things. 'Bound'
-- variables are de Bruijn indexes, and are used only in the scope of the
-- binder that binds the index. All both have string values that represent the
-- stored display name of the variable, for pretty printing.

data Variable
  = Free FreeVar
  | Bound String BoundVar
  | Meta MetaVar
  deriving (Show)


-- | The name of a variable.

name :: Variable -> String
name (Free (FreeVar n)) = n
name (Bound n _)        = n
name (Meta i)           = "?" ++ show i


-- | Equality of variables is by the parts which identify them, so names for
-- 'Free' variables, and identifying numbers for 'Bound'.

instance Eq Variable where
  Free x    == Free y    = x == y
  Bound _ i == Bound _ j = i == j
  Meta m    == Meta n    = m == n
  _         == _         = False



-- | A free variable is just a 'String' but we use a @newtype@ to prevent
-- accidentally using it for the wrong things.

newtype FreeVar = FreeVar String
  deriving (Eq,Show,Generic)



-- | A bound variable is just an 'Int' but we use a @newtype@ to prevent
-- accidentally using it for the wrong things.

newtype BoundVar = BoundVar Int
  deriving (Eq,Show,Generic)



-- | A meta variable is just an 'Int' but we use a @newtype@ to prevent
-- accidentally using it for the wrong things.

newtype MetaVar = MetaVar Int
  deriving (Eq,Show,Num,Ord,Generic)







-- * Freshening names



-- | We can freshen a set of names relative to some other names. This ensures
-- that the freshened names are distinct from the specified names, and also
-- distinct from one another.

freshen :: [String] -> [String] -> [String]
freshen others ns = reverse (go (reverse ns))
  where
    go :: [String] -> [String]
    go [] = []
    go (oldN:oldNs) = newN:newNs
      where
        newNs = go oldNs
        newN = freshenName (newNs ++ others) oldN


-- | We can freshen a single name relative to some other set of names,
-- ensuring that the new name is distinct from all the specified names.

freshenName :: [String] -> String -> String
freshenName others n
  | n == "_" = n
  | n `elem` others = freshenName others (n ++ "'")
  | otherwise = n