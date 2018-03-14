{-# OPTIONS -Wall #-}






module PlutusCore.ElabError where

import Utils.Pretty
import Utils.Vars
import PlutusCore.Term





data ElabError = TypeConstructorAlreadyDeclared String
               | TypeNameAlreadyDeclared String
               | TermConstructorAlreadyDeclared String
               | TermNameAlreadyDeclared String
               | TermNameAlreadyDefined String
               | TypeConstructorNotInScope String
               | TypeNameNotInScope String
               | TermConstructorNotInScope String
               | TermNameNotInScope String
               | TypeVariableNotInScope String
               | TermVariableNotInScope String
               | RepeatedConstructorsInCase [String]
               | MissingConstructorsInCase [String]
               | UnknownBuiltinName String
               | UnknownCompBuiltinName String
               | LanguageOptionNoConstructors
               | LanguageOptionFixedPointTypes
               | TermDeclarationTypeIsNotType String Term Kind
               | TermConstructorArgumentKindIsNotType String Term Kind
               | FunTypeArgumentIsNotType Term Kind
               | FunTypeReturnIsNotType Term Kind
               | TypeConstructorWrongNumberOfArguments String Int Int
               | TypeConstructorWrongArgumentKind String Term Kind Kind
               | FixBodyNotType Term Kind
               | CompArgumentNotType Term Kind
               | ForallBodyNotType Type Kind
               | TypeApplicationArgumentKindMismatch Term Kind Kind
               | TypeApplicationOfNonFunctionKind Term Kind
               | CannotSynthKindOfNonType Term
               | TypeIsNotTypeValue Term
               | TermIsNotTermValue Term
               | TermConstructorCheckedAtWrongType String String String
               | TermConstructorWrongNumberOfArguments String Int Int
               | CaseScrutineeNotConstructedData Term Term
               | InstantiationAtWrongKind Term Term Kind Kind
               | InstantiationOfNonForallType Term Term
               | ApplicationOfNonFunctionType Term Term
               | CannotUnwrapNonFixedPointType Term Term
               | BindBodyNotCompType Term Term
               | BindArgumentNotCompType Term Term
               | BuiltinWrongNumberOfArguments String Int Int
               | CannotSynthType Term
               | ClauseConstructorWrongType String String String
               | ClauseConstructorWrongNumberOfArguments String Int Int
               | VariablesNotEqual Variable Variable
               | TermsNotEqual Term Term
               




prettyElabError :: ElabError -> String
prettyElabError (TypeConstructorAlreadyDeclared n) =
  "The type constructor `" ++ n ++ "` has already been declared."
prettyElabError (TypeNameAlreadyDeclared n) =
  "The type name `" ++ n ++ "` has already been declared."
prettyElabError (TermConstructorAlreadyDeclared n) =
  "The term constructor `" ++ n ++ "` has already been declared."
prettyElabError (TermNameAlreadyDeclared n) =
  "The term name `" ++ n ++ "` has already been declared."
prettyElabError (TermNameAlreadyDefined n) =
  "The term name `" ++ n ++ "` has already been defined."
prettyElabError (TypeConstructorNotInScope n) =
  "The type constructor `" ++ n ++ "` is not in scope."
prettyElabError (TypeNameNotInScope n) =
  "The type name `" ++ n ++ "` is not in scope."
prettyElabError (TermConstructorNotInScope n) =
  "The term constructor `" ++ n ++ "` is not in scope."
prettyElabError (TermNameNotInScope n) =
  "The term name `" ++ n ++ "` is not in scope."
prettyElabError (TypeVariableNotInScope n) =
  "The type variable `" ++ n ++ "` is not in scope."
prettyElabError (TermVariableNotInScope n) =
  "The term variable `" ++ n ++ "` is not in scope."
prettyElabError (RepeatedConstructorsInCase ns) =
  "The following constructors have repeated case clauses: " ++ unwords ns
prettyElabError (MissingConstructorsInCase ns) =
  "The following constructors have missing case clauses: " ++ unwords ns
prettyElabError (UnknownBuiltinName n) =
  "There is no builtin named `" ++ n ++ "`."
prettyElabError (UnknownCompBuiltinName n) =
  "There is no compbuiltin named `" ++ n ++ "`."
prettyElabError LanguageOptionNoConstructors =
  "The language option NoConstructors is currently enabled. Data declarations are disabled with this option. Remove it to enable data declarations."
prettyElabError LanguageOptionFixedPointTypes =
  "The language options FixedPointTypes is not currently enabled. Fixed point types are not enabled without this option. Add it to enable fixed point types."
prettyElabError (TermDeclarationTypeIsNotType n a k) =
  "The declaration for the term name `" ++ n
  ++ "` declares it to have the type `" ++ pretty a
  ++ "` which has kind `" ++ prettyKind k
  ++ "` instead of kind `" ++ prettyKind TypeK
  ++ "`"
prettyElabError (TermConstructorArgumentKindIsNotType n a k) =
  "The term constructor `" ++ n
  ++ "` is declared to have an argument of type `" ++ pretty a
  ++ "` which is of kind `" ++ prettyKind k
  ++ "` but should be of kind `" ++ prettyKind TypeK
  ++ "`."
prettyElabError (FunTypeArgumentIsNotType a k) =
  "The argument type of a function type should be of kind `" ++ prettyKind TypeK
  ++ "` but the type `" ++ pretty a
  ++ "` is of kind `" ++ prettyKind k
  ++ "`."
prettyElabError (FunTypeReturnIsNotType a k) =
  "The return type of a function type should be of kind `" ++ prettyKind TypeK
  ++ "` but the type `" ++ pretty a
  ++ "` is of kind `" ++ prettyKind k
  ++ "`."
prettyElabError (TypeConstructorWrongNumberOfArguments n l l') =
  "The type constructor `" ++ n
  ++ "` expects " ++ show l
  ++ " arguments but was given " ++ show l'
  ++ "."
prettyElabError (TypeConstructorWrongArgumentKind n a k k') =
  "The type constructor `" ++ n
  ++ "` expects an argument of kind `" ++ prettyKind k
  ++ "` but was given `" ++ pretty a
  ++ "` which is of kind `" ++ prettyKind k'
  ++ "`."
prettyElabError (FixBodyNotType a k) =
  "Fixed point types must have bodies of kind `" ++ prettyKind TypeK
  ++ "` but the type `" ++ pretty a
  ++ "` has kind `" ++ prettyKind k
  ++ "`."
prettyElabError (CompArgumentNotType a k) =
  "The argument of the comp type constructor should be of kind `" ++ prettyKind TypeK
  ++ "` but `" ++ pretty a
  ++ "` is of kind `" ++ prettyKind k
  ++ "`."
prettyElabError (ForallBodyNotType a k) =
  "Forall types must have bodies of kind `" ++ prettyKind TypeK
  ++ "` but the type `" ++ pretty a
  ++ "` has kind `" ++ prettyKind k
  ++ "`."
prettyElabError (TypeApplicationArgumentKindMismatch a k k') =
  "The type function argument `" ++ pretty a
  ++ "` is expected to be of kind `" ++ prettyKind k
  ++ "` but is actually of kind `" ++ prettyKind k'
  ++ "`."
prettyElabError (TypeApplicationOfNonFunctionKind a k) =
  "The type function `" ++ pretty a
  ++ "` should have a function kind but instead has kind `" ++ prettyKind k
  ++ "`."
prettyElabError (CannotSynthKindOfNonType m) =
  "The kind of `" ++ pretty m
  ++ "` cannot be synthesized because it is not a type."
prettyElabError (TypeIsNotTypeValue a) =
  "The type `" ++ pretty a
  ++ "` should be a type value but is not."
prettyElabError (TermIsNotTermValue m) =
  "The term `" ++ pretty m
  ++ "` should be a term value but is not."
prettyElabError (TermConstructorCheckedAtWrongType n c c') =
  "The term constructor `" ++ n
  ++ "` constructs a term for the type constructor `" ++ c
  ++ "` but is being checked the type constructor `" ++ c'
  ++ "`."
prettyElabError (TermConstructorWrongNumberOfArguments n l l') =
  "The term constructor `" ++ n
  ++ "` expects " ++ show l
  ++ " arguments but was given " ++ show l'
  ++ "."
prettyElabError (CaseScrutineeNotConstructedData m a) =
  "The case scrutinee `" ++ pretty m
  ++ "` should have a constructed data type but instead has the type `" ++ pretty a
  ++ "`."
prettyElabError (InstantiationAtWrongKind m a k k') =
  "The polymorphic term `" ++ pretty m
  ++ "` should be instantiated at a type of kind `" ++ prettyKind k
  ++ "` but `" ++ pretty a
  ++ "` is of kind `" ++ prettyKind k'
  ++ "`."
prettyElabError (InstantiationOfNonForallType m a) =
  "The term `" ++ pretty m
  ++ "` is being instantiated and therefore should have a forall type, but actually has the type `" ++ pretty a
  ++ "`."
prettyElabError (ApplicationOfNonFunctionType m a) =
  "The term `" ++ pretty m
  ++ "` is being applied and therefore should have a function type, but actually has the type `" ++ pretty a
  ++ "`."
prettyElabError (CannotUnwrapNonFixedPointType m a) =
  "The term `" ++ pretty m
  ++ "` is being unwrapped and therefore should have a fixed point type, but actually has the type `" ++ pretty a
  ++ "`."
prettyElabError (BindBodyNotCompType m a) =
  "The term `" ++ pretty m
  ++ "` is the body of a bind and therefore should have a comp type, but actually has the type `" ++ pretty a
  ++ "`."
prettyElabError (BindArgumentNotCompType m a) =
  "The term `" ++ pretty m
  ++ "` is the argument of a bind and therefore should have a comp type, but actually has the type `" ++ pretty a
  ++ "`."
prettyElabError (BuiltinWrongNumberOfArguments n l l') =
  "The builtin `" ++ n
  ++ "` expects " ++ show l
  ++ " arguments but was given " ++ show l'
  ++ "."
prettyElabError (CannotSynthType m) =
  "The type of the term `" ++ pretty m
  ++ "` cannot be synthesized."
prettyElabError (ClauseConstructorWrongType n c c') =
  "The clause for the term constructor `" ++ n
  ++ "` expects a case scrutinee with the type constructor `" ++ c
  ++ "` but the scrutinee is actually for the type constructor `" ++ c'
  ++ "`."
prettyElabError (ClauseConstructorWrongNumberOfArguments n l l') =
  "The clause for the term constructor `" ++ n
  ++ "` should expect " ++ show l
  ++ " arguments but actually expects " ++ show l'
  ++ "."
prettyElabError (VariablesNotEqual x y) =
  "The following variables should be equal but are not: "
  ++ unwords (map name [x,y])
prettyElabError (TermsNotEqual m m') =
  "The following terms should be equal but are not: "
  ++ unwords (map pretty [m,m'])