{-# OPTIONS -Wall #-}

module PlutusCore.LanguageOptions where



data LanguageOption = NoConstructors
                    | FixedPointTypes
  deriving (Eq,Ord,Show)