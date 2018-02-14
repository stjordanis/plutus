{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}







module PlutusCore.Elaboration where

import Utils.ABT
--import Utils.Elaborator hiding (openScope)
--import Utils.Names
import Utils.Pretty
import Utils.ProofDeveloper hiding (Decomposer,ElabError,Context)
--import Utils.Unifier
import Utils.Vars
import PlutusCore.Evaluation
import PlutusCore.Term
import PlutusCore.Program
import PlutusCore.Contexts
import PlutusCore.Elaborator
import PlutusCore.Judgments
import PlutusCore.EvaluatorTypes
import PlutusShared.Qualified

import Control.Monad.Except
--import Control.Monad.State
--import Data.Functor.Identity
import Data.List
--import Data.Maybe (isJust)

--import Debug







instance Decomposable () ElabError Judgment where
  decompose (ElabProgramJ prog) = programJ prog
  decompose (ElabModuleJ ls mdl) = moduleJ ls mdl
  decompose (ElabDeclJ l ls' nomctx decl) =
    declJ l ls' nomctx decl
  decompose (ElabAltJ l ls' nomctx alt ksigs) =
    altJ l ls' nomctx alt ksigs
  decompose (IsTypeJ ctx a) = isTypeJ ctx a
  decompose (IsTypeValueJ a) = isTypeValueJ a
  decompose (IsTermValueJ m) = isTermValueJ m
  decompose (CheckJ ctx a m) = checkJ ctx a m
  decompose (SynthJ ctx m) = synthJ ctx m
  decompose (ClauseJ ctx tc as t cl) = clauseJ ctx tc as t cl
  decompose (EqualJ ctx a b) = equalJ ctx a b
  decompose (EqualAllJ ctx a bs) = equalAllJ ctx a bs








openScope :: HypotheticalContext -> Scope PlutusSig -> ([FreeVar], [String], Term)
openScope ctx sc =
  let ns = names sc
      oldNs = map variableName ctx
      freshNs = map FreeVar (freshen oldNs ns)
      newVars = [ Var (Free n) | n <- freshNs ]
      newNames = [ x | FreeVar x <- freshNs ]
      m = instantiate sc newVars
  in (freshNs, newNames, m)








nominalContextToTypeEnv :: Context -> QualifiedEnv
nominalContextToTypeEnv (Context { currentModule = currl
                                 , nominalContext = (ls,ds)
                                 }) =
  (ls >>= moduleToTypeEnv) ++ (ds >>= declarationToTypeEnv currl)
  where
    moduleToTypeEnv :: Module -> QualifiedEnv
    moduleToTypeEnv (Module l' _ _ ds') =
      ds' >>= declarationToTypeEnv l'
    
    declarationToTypeEnv :: String -> Declaration -> QualifiedEnv
    declarationToTypeEnv l (TypeDeclaration n t) =
      [(QualifiedName l n, t)]
    declarationToTypeEnv _ _ = []






freshModuleName :: [Module] -> String -> Decomposer ()
freshModuleName ls l =
  unless (not (any (\(Module l' _ _ _) -> l == l') ls))
    (failure
      (ElabError
        ("The module name " ++ l ++ " is already in used")))





freshTypeConstructor :: [Declaration] -> String -> Decomposer ()
freshTypeConstructor ds n =
  unless (all freshInDeclaration ds)
    (failure
      (ElabError
        ("The data type " ++ n
          ++ " has already been declared in this module")))
  where
    freshInDeclaration :: Declaration -> Bool
    freshInDeclaration (DataDeclaration c _ _) = n /= c
    freshInDeclaration _ = True






freshTypeName :: [Declaration] -> String -> Decomposer ()
freshTypeName ds n =
  unless (all freshInDeclaration ds)
    (failure
      (ElabError
        ("The type name " ++ n
          ++ " has already been declared in this module")))
  where
    freshInDeclaration :: Declaration -> Bool
    freshInDeclaration (TypeDeclaration n' _) = n /= n'
    freshInDeclaration _ = True






freshTermConstructor :: [Declaration] -> String -> Decomposer ()
freshTermConstructor ds n =
  unless (all freshInDeclaration ds)
    (failure
      (ElabError
        ("The term constructor " ++ n
          ++ " has already been declared in this module")))
  where
    freshInDeclaration :: Declaration -> Bool
    freshInDeclaration (DataDeclaration _ _ alts) =
      all freshInAlt alts
    freshInDeclaration _ = True
    
    freshInAlt :: Alt -> Bool
    freshInAlt (Alt n' _) = n /= n'






freshTermName :: [Declaration] -> String -> Decomposer ()
freshTermName ds nm =
  unless (all freshInDeclaration ds)
    (failure
      (ElabError
        ("The term name " ++ nm
          ++ " has already been declared in this module")))
  where
    freshInDeclaration :: Declaration -> Bool
    freshInDeclaration (TermDeclaration nm' _) = nm /= nm'
    freshInDeclaration _ = True






undefinedTermName :: [Declaration] -> String -> Decomposer ()
undefinedTermName ds n =
  unless (all undefinedInDeclaration ds)
    (failure
      (ElabError
        ("The term name " ++ n
          ++ " has already been defined in this module")))
  where
    undefinedInDeclaration :: Declaration -> Bool
    undefinedInDeclaration (TermDefinition n' _ ) = n /= n'
    undefinedInDeclaration _ = True







typeNameInContext
  :: Context -> QualifiedName -> Decomposer Kind
typeNameInContext ctx@(Context { currentModule = currl
                               , nominalContext = (ls,ds)
                               })
                  nu@(QualifiedName l nm) =
  if currl == l
    then
      findInDeclarations ds
    else
      findInModules ls
  where
    findInModules [] = err
    findInModules (Module l' _ _ ds':ls')
      | l == l' = findInDeclarations ds'
      | otherwise = findInModules ls'
    
    findInDeclarations [] = err
    findInDeclarations (TypeDeclaration nm' t:ds')
      | nm == nm' = goal (IsTypeJ ctx t)
      | otherwise = findInDeclarations ds'
    findInDeclarations (_:ds') = findInDeclarations ds'
    
    err = failure
           (ElabError
             ("Type name not in scope: " ++ prettyQualifiedName nu))





typeConstructorInContext
  :: Context -> QualifiedConstructor -> Decomposer [Kind]
typeConstructorInContext (Context { currentModule = currl
                                  , nominalContext = (ls,ds)
                                  })
                         kap@(QualifiedConstructor l nm) =
  if currl == l
    then
      findInDeclarations ds
    else
      findInModules ls
  where
    findInModules [] = err
    findInModules (Module l' _ _ ds':ls')
      | l == l' = findInDeclarations ds'
      |otherwise = findInModules ls'
    
    findInDeclarations [] = err
    findInDeclarations (DataDeclaration nm' ksigs _:ds')
      | nm == nm' = return [ k | KindSig _ k <- ksigs ]
      | otherwise = findInDeclarations ds'
    findInDeclarations (_:ds') = findInDeclarations ds'
    
    err = failure
           (ElabError
             ("Type constructor not in scope: "
               ++ prettyQualifiedConstructor kap))



termConstructorInContext
  :: Context
  -> QualifiedConstructor
  -> Decomposer ([Scope PlutusSig], QualifiedConstructor)
termConstructorInContext (Context { currentModule = currl
                                  , nominalContext = (ls,ds)
                                  })
                         c@(QualifiedConstructor l nm) =
  if currl == l
    then
      findInDeclarations l ds
    else
      findInModules ls
  where
    findInModules [] = err
    findInModules (Module l' _ _ ds':ls')
      | l == l' = findInDeclarations l' ds'
      | otherwise = findInModules ls'
    
    findInDeclarations _ [] = err
    findInDeclarations l' (DataDeclaration nm' _ alts:ds') =
      case findAlt alts of
        Nothing -> findInDeclarations l' ds'
        Just ascs -> return (ascs, QualifiedConstructor l' nm')
    findInDeclarations l' (_:ds') = findInDeclarations l' ds'
    
    findAlt [] = Nothing
    findAlt (Alt nm' ascs:alts)
      | nm == nm' = Just ascs
      | otherwise = findAlt alts
    
    err = failure
           (ElabError
             ("Term constructor not in scope: "
               ++ prettyQualifiedConstructor c))






termNameInContext
  :: Context -> QualifiedName -> Decomposer Term
termNameInContext ctx@(Context { currentModule = currl
                               , nominalContext = (ls,ds)
                               })
                  n@(QualifiedName l nm) =
  if currl == l
    then
      findInDeclarations ds
    else
      findInModules ls
  where
    findInModules [] = err
    findInModules (Module l' _ _ ds':ls')
      | l == l' = findInDeclarations ds'
      | otherwise = findInModules ls'
    
    findInDeclarations [] = err
    findInDeclarations (TermDeclaration nm' tv:ds')
      | nm == nm' = return tv
      | otherwise = findInDeclarations ds'
    findInDeclarations (_:ds') = findInDeclarations ds'
    
    err = failure
           (ElabError
             ("Term name not in scope: " ++ prettyQualifiedName n))






typeVariableInHypotheticalContext
  :: HypotheticalContext -> String -> Decomposer Kind
typeVariableInHypotheticalContext [] y =
  failure (ElabError ("Type variable not in scope: " ++ y))
typeVariableInHypotheticalContext (HasKind x k : _) y | x == y =
  return k
typeVariableInHypotheticalContext (_ : hypctx) y =
  typeVariableInHypotheticalContext hypctx y






termVariableInHypotheticalContext
  :: HypotheticalContext -> String -> Decomposer Term
termVariableInHypotheticalContext [] y =
  failure (ElabError ("Term variable not in scope: " ++ y))
termVariableInHypotheticalContext (HasType x u : _) y | x == y =
  return u
termVariableInHypotheticalContext (_ : hypctx) y =
  termVariableInHypotheticalContext hypctx y







noRepeatedConstructors :: [Clause] -> Decomposer ()
noRepeatedConstructors cls =
  do let cs = [ c | Clause c :$: [_] <- cls ]
         uniqueCs = nub cs
         repeats = nub (cs \\ uniqueCs)
     unless (null repeats)
       (failure
         (ElabError
           ("The constructors "
             ++ unwords [ "`" ++ prettyQualifiedConstructor c ++ "`"
                        | c <- repeats
                        ]
             ++ " occur in distinct clauses of a case term")))






coversAllConstructors :: Context
                      -> QualifiedConstructor
                      -> [Clause]
                      -> Decomposer ()
coversAllConstructors ctx (QualifiedConstructor l nm) cls =
  do let cs = [ QualifiedConstructor l connm
              | connm <- extractCons ctx
              ]
         missing = cs \\ [ c | Clause c :$: [_] <- cls ]
     unless (null missing)
       (failure
         (ElabError
           ("The constructors "
             ++ unwords [ "`" ++ prettyQualifiedConstructor c ++ "`"
                        | c <- missing
                        ]
             ++ " are missing clauses in a case term")))
  where
    extractCons (Context { currentModule = l'
                         , nominalContext = (ls,ds)
                         })
      | l == l' = extractFromDeclarations ds
      | otherwise = extractFromModules ls
    
    extractFromModules [] = []
    extractFromModules (Module l' _ _ ds:ls)
      | l == l' = extractFromDeclarations ds
      | otherwise = extractFromModules ls
    
    extractFromDeclarations [] = []
    extractFromDeclarations (DataDeclaration nm' _ alts:ds)
      | nm == nm' = [ connm | Alt connm _ <- alts ]
      | otherwise = extractFromDeclarations ds
    extractFromDeclarations (_:ds) = extractFromDeclarations ds






signatureOfBuiltin :: String -> Decomposer ([Term], Term)
signatureOfBuiltin n =
  case lookup n builtinSigs of
    Nothing ->
      failure
        (ElabError ("No builtin named `" ++ n ++ "`"))
    Just s -> return s
  where
    builtinSigs =
      
      [ ("addInteger",       ([integerTH, integerTH], integerTH))
      , ("subtractInteger",  ([integerTH, integerTH], integerTH))
      , ("multiplyInteger",  ([integerTH, integerTH], integerTH))
      , ("divideInteger",    ([integerTH, integerTH], integerTH))
      , ("remainderInteger", ([integerTH, integerTH], integerTH))
      , ("lessThanInteger"
        ,  ( [integerTH, integerTH]
           -- , conTH (QualifiedConstructor "Prelude" "Bool") []
           , scottBool
           ))
      , ("lessThanEqualsInteger"
        , ( [integerTH, integerTH]
          -- , conTH (QualifiedConstructor "Prelude" "Bool") []
          , scottBool
          ))
      , ("greaterThanInteger"
        , ( [integerTH, integerTH]
          -- , conTH (QualifiedConstructor "Prelude" "Bool") []
          , scottBool
          ))
      , ("greaterThanEqualsInteger"
        , ( [integerTH, integerTH]
          -- , conTH (QualifiedConstructor "Prelude" "Bool") []
          , scottBool
          ))
      , ("equalsInteger"
        ,  ( [integerTH, integerTH]
           -- , conTH (QualifiedConstructor "Prelude" "Bool") []
           , scottBool
           ))
      , ("integerToFloat", ([integerTH], floatTH))
      , ("integerToByteString", ([integerTH], byteStringTH))
      
      
      , ("addFloat", ([floatTH, floatTH], floatTH))
      , ("subtractFloat", ([floatTH, floatTH], floatTH))
      , ("multiplyFloat", ([floatTH, floatTH], floatTH))
      , ("divideFloat", ([floatTH, floatTH], floatTH))
      , ("lessThanFloat"
        ,  ( [floatTH, floatTH]
           -- , conTH (QualifiedConstructor "Prelude" "Bool") []
           , scottBool
           ))
      , ("lessThanEqualsFloat"
        , ( [floatTH, floatTH]
          -- , conTH (QualifiedConstructor "Prelude" "Bool") []
          , scottBool
          ))
      , ("greaterThanFloat"
        , ( [floatTH, floatTH]
          -- , conTH (QualifiedConstructor "Prelude" "Bool") []
          , scottBool
          ))
      , ("greaterThanEqualsFloat"
        , ( [floatTH, floatTH]
          -- , conTH (QualifiedConstructor "Prelude" "Bool") []
          , scottBool
          ))
      , ("equalsFloat"
        ,  ( [floatTH, floatTH]
           -- , conTH (QualifiedConstructor "Prelude" "Bool") []
           , scottBool
           ))
      , ("ceil", ([floatTH], integerTH))
      , ("floor", ([floatTH], integerTH))
      , ("round", ([floatTH], integerTH))
      
      
      , ("concatenate", ([byteStringTH, byteStringTH], byteStringTH))
      , ("takeByteString", ([integerTH, byteStringTH], byteStringTH))
      , ("dropByteString", ([integerTH, byteStringTH], byteStringTH))
      , ("sha2_256", ([byteStringTH], byteStringTH))
      , ("sha3_256", ([byteStringTH], byteStringTH))
      , ("equalsByteString"
        ,  ( [byteStringTH, byteStringTH]
           -- , conTH (QualifiedConstructor "Prelude" "Bool") []
           , scottBool
           ))
      ]
    
    scottUnit :: Type
    scottUnit = forallTH "a" TypeK
                  (funTH (Var (Free (FreeVar "a")))
                         (Var (Free (FreeVar "a"))))
    scottBool :: Type
    scottBool = forallTH "r" TypeK
                  (funTH (funTH scottUnit (Var (Free (FreeVar "r"))))
                    (funTH (funTH scottUnit (Var (Free (FreeVar "r"))))
                           (Var (Free (FreeVar "r")))))





synthCompBuiltin :: String -> Decomposer Term
synthCompBuiltin "txhash" = return byteStringTH
synthCompBuiltin "blocknum" = return integerTH
synthCompBuiltin "blocktime" =
  return (conTH (QualifiedConstructor "(con" "DateTime") [])
synthCompBuiltin n =
  failure (ElabError ("Unknown computation builtin: " ++ n))







programJ :: Program -> Decomposer ()
programJ (Program modules) =
  forM_ (zip (inits modules) modules) $ \(ls, l) ->
    goal (ElabModuleJ ls l)






moduleJ :: [Module] -> Module -> Decomposer ()
moduleJ ls (Module l ls' (Exports tyexp tmexp) decls) =
  do freshModuleName ls l
     typeExportsAreValid tyexp decls
     termExportsAreValid tmexp decls
     forM_ (zip (inits decls) decls) $ \(ds,d) ->
       goal (ElabDeclJ l ls' (ls,ds) d)
  where
    typeExportsAreValid :: [TypeExport] -> [Declaration] -> Decomposer ()
    typeExportsAreValid [] _ = return ()
    typeExportsAreValid (TypeNameExport nu : tx) ds =
      if any (declaresTypeName nu) ds
         then typeExportsAreValid tx ds
         else failure
                (ElabError
                  ("Could not export the type name `" ++ nu
                    ++ "` since the module " ++ l ++ " does not declare it"))
    typeExportsAreValid (TypeConstructorExport kap cs : tx) ds =
      case find (declaresData kap) ds of
        Just (DataDeclaration _ _ alts) ->
          case cs \\ [ c | Alt c _ <- alts ] of
            [] -> typeExportsAreValid tx ds
            missing ->
              failure
                (ElabError
                  ("Could not export the term constructors "
                    ++ intercalate ", " [ "`" ++ c ++ "`" | c <- missing ]
                    ++ " since the module " ++ l ++ " does not declare them"))
        _ ->
          failure
            (ElabError
              ("Could not export the type constructor `" ++ kap
                ++ "` since the module " ++ l ++ " does not declare it"))
    
    declaresTypeName :: String -> Declaration -> Bool
    declaresTypeName nu (TypeDeclaration nu' _) = nu == nu'
    declaresTypeName _ _ = False
    
    declaresData :: String -> Declaration -> Bool
    declaresData kap (DataDeclaration kap' _ _) = kap == kap'
    declaresData _ _ = False
    
    termExportsAreValid :: [String] -> [Declaration] -> Decomposer ()
    termExportsAreValid ns ds =
      case ns \\ [ n | TermDeclaration n _ <- ds ] of
        [] -> return ()
        missing ->
          failure
            (ElabError
              ("Could not export the term names "
                ++ intercalate ", " [ "`" ++ n ++ "`" | n <- missing ]
                ++ " since the module " ++ l ++ " does not declare them"))
--     data TypeExport = TypeNameExport String
--                 | TypeConstructorExport String [String]
-- 
-- data Exports = Exports [TypeExport] [String]





declJ :: String
      -> [String]
      -> NominalContext
      -> Declaration
      -> Decomposer ()
declJ l ls' (ls,ds) (DataDeclaration tcn ksigs alts) =
  do freshTypeConstructor ds tcn
     let nomctxAddition = DataDeclaration tcn ksigs []
     forM_ alts $ \alt ->
       goal (ElabAltJ
              l
              ls'
              (ls, nomctxAddition:ds)
              alt
              ksigs)
declJ l ls' nomctx@(_,ds) (TypeDeclaration tnm u) =
  do freshTypeName ds tnm
     goal (IsTypeValueJ u)
     _ <- goal (IsTypeJ (Context l ls' nomctx []) u)
     return ()
declJ l ls' nomctx@(_,ds) (TermDeclaration nm t) =
  do freshTermName ds nm
     k <- goal (IsTypeJ (Context l ls' nomctx []) t)
     case k of
       TypeK -> return ()
       _ -> failure
              (ElabError
                ("The term name " ++ nm ++ " has been declared with the type "
                  ++ pretty t ++ " which should have kind "
                  ++ prettyKind TypeK ++ " but which actually has kind "
                  ++ prettyKind k))
declJ l ls' nomctx@(_,ds) (TermDefinition nm v) =
  do undefinedTermName ds nm
     u <- termNameInContext
            (Context l ls' nomctx [])
            (QualifiedName l nm)
     goal (IsTermValueJ v)
     let tenv = nominalContextToTypeEnv (Context l ls' nomctx [])
         normal_u = evaluateType tenv u
     goal (CheckJ (Context l ls' nomctx []) normal_u v)





altJ :: String
     -> [String]
     -> NominalContext
     -> Alt
     -> [KindSig]
     -> Decomposer ()
altJ l ls' nomctx@(_,ds) (Alt cn ascs) ksigs =
  do freshTermConstructor ds cn
     let hypctx = [ HasKind x k | KindSig x k <- ksigs ]
         xs =  [ Var (Free (FreeVar x)) | KindSig x _ <- ksigs ]
     forM_ ascs $ \asc ->
       do k' <- goal
                  (IsTypeJ
                    (Context l ls' nomctx hypctx)
                    (instantiate asc xs))
          unless (k' == TypeK)
            (failure
              (ElabError
                ("Term constructors can only specify types for arguments but "
                  ++ cn
                  ++ " has been specified as having something of kind "
                  ++ prettyKind k')))
          return ()
     return ()







isTypeJ :: Context -> Term -> Decomposer Kind
isTypeJ ctx (Var (Free (FreeVar x))) =
  typeVariableInHypotheticalContext (hypotheticalContext ctx) x
isTypeJ _ (Var (Bound _ _)) =
  failure
    (ElabError
      ("Cannot synthesize the kind of a bound type variable."))
isTypeJ ctx (DecnameT n :$: []) =
  typeNameInContext ctx n
isTypeJ ctx (FunT :$: [a,b]) =
  do k <- goal (IsTypeJ ctx (instantiate0 a))
     unless (k == TypeK)
       (failure
         (ElabError
           ("Kind of " ++ pretty (instantiate0 a)
             ++ " should be (type) but is actually "
             ++ prettyKind k)))
     k' <- goal (IsTypeJ ctx (instantiate0 b))
     unless (k' == TypeK)
       (failure
         (ElabError
           ("Kind of " ++ pretty (instantiate0 b)
             ++ " should be (type) but is actually "
             ++ prettyKind k')))
     return TypeK
isTypeJ ctx (ConT c :$: as) =
  do ks <- typeConstructorInContext ctx c
     unless (length as == length ks)
       (failure
         (ElabError
           ("Type constructor `" ++ prettyQualifiedConstructor c
             ++ "` expects " ++ show (length ks)
             ++ " arguments but was given "
             ++ show (length as))))
     zipWithM_
       (\a k -> 
         do k' <- goal (IsTypeJ ctx (instantiate0 a))
            unless (k == k')
              (failure
                (ElabError
                  ("Type constructor `" ++ prettyQualifiedConstructor c
                    ++ "` expects an argument of kind `"
                    ++ prettyKind k
                    ++ "` but was given an argument of kind `"
                    ++ prettyKind k'
                    ++ "`")))
            return ())
       as
       ks
     return TypeK
isTypeJ ctx (CompT :$: [a]) =
  do k <- goal (IsTypeJ ctx (instantiate0 a))
     unless (k == TypeK)
       (failure
         (ElabError
           ("Kind of " ++ pretty (instantiate0 a)
             ++ " should be (type) but is actually "
             ++ prettyKind k)))
     return TypeK
isTypeJ ctx (ForallT k :$: [sc]) =
  do let (_, [n], a) = openScope (hypotheticalContext ctx) sc
         ctx' = ctx { hypotheticalContext =
                        HasKind n k : hypotheticalContext ctx
                    }
     k' <- goal (IsTypeJ ctx' a)
     unless (k' == TypeK)
       (failure
         (ElabError
           ("Kind of " ++ pretty a
             ++ " should be (type) but is actually "
             ++ prettyKind k')))
     return TypeK
isTypeJ _ (IntegerT :$: []) =
  return TypeK
isTypeJ _ (FloatT :$: []) =
  return TypeK
isTypeJ _ (ByteStringT :$: []) =
  return TypeK
isTypeJ ctx (LamT k :$: [sc]) =
  do let (_, [n], a) = openScope (hypotheticalContext ctx) sc
         ctx' = ctx { hypotheticalContext =
                        HasKind n k : hypotheticalContext ctx
                    }
     k' <- goal (IsTypeJ ctx' a)
     return (FunK k k')
isTypeJ ctx (AppT :$: [a,b]) =
  do k <- goal (IsTypeJ ctx (instantiate0 a))
     case k of
       FunK k' k'' ->
         do k''' <- goal (IsTypeJ ctx (instantiate0 b))
            unless (k' == k''')
              (failure
                (ElabError
                  ("Kind of " ++ pretty (instantiate0 b)
                    ++ " should be "
                    ++ prettyKind k'
                    ++ " but is actually "
                    ++ prettyKind k''')))
            return k''
       _ ->
         failure
           (ElabError
             ("Kind of " ++ pretty (instantiate0 a)
               ++ " should be a function but is actually "
               ++ prettyKind k))
isTypeJ _ m =
  failure
    (ElabError
      ("Cannot synthesize the kind of non-type `" ++ pretty m ++ "`"))






isTypeValueJ :: Term -> Decomposer ()
isTypeValueJ (Var _) =
  return ()
isTypeValueJ (DecnameT _ :$: []) =
  return ()
isTypeValueJ (FunT :$: [a,b]) =
  do goal (IsTypeValueJ (instantiate0 a))
     goal (IsTypeValueJ (instantiate0 b))
isTypeValueJ (ConT _ :$: as) =
  forM_ as $ \a ->
    goal (IsTypeValueJ (instantiate0 a))
isTypeValueJ (CompT :$: [a]) =
  goal (IsTypeValueJ (instantiate0 a))
isTypeValueJ (LamT _ :$: [_]) =
  return ()
isTypeValueJ (ForallT _ :$: [_]) =
  return ()
isTypeValueJ (IntegerT :$: []) =
  return ()
isTypeValueJ (FloatT :$: []) =
  return ()
isTypeValueJ (ByteStringT :$: []) =
  return ()
isTypeValueJ a =
  failure
    (ElabError
      ("The type `" ++ pretty a ++ "` is not a value"))






isTermValueJ :: Term -> Decomposer ()
isTermValueJ (Abst :$: [_]) =
  return ()
isTermValueJ (Lam :$: [_]) =
  return ()
isTermValueJ (Con _ :$: ms) =
  forM_ ms $ \m ->
    goal (IsTermValueJ (instantiate0 m))
isTermValueJ (Success :$: [m]) =
  goal (IsTermValueJ (instantiate0 m))
isTermValueJ (Failure :$: []) =
  return ()
isTermValueJ (CompBuiltin _ :$: []) =
  return ()
isTermValueJ (Bind :$: [m,_]) =
  goal (IsTermValueJ (instantiate0 m))
isTermValueJ m =
  failure
    (ElabError
      ("The term `" ++ pretty m ++ "` is not a value"))






checkJ :: Context -> Term -> Term -> Decomposer ()
checkJ ctx (ForallT k :$: [sc]) (Abst :$: [sc']) =
  do let ([x], [n], a) = openScope (hypotheticalContext ctx) sc
         ctx' = ctx { hypotheticalContext =
                        HasKind n k : hypotheticalContext ctx
                    }
         m = instantiate sc' [Var (Free x)]
         tenv = nominalContextToTypeEnv ctx
         normal_a = evaluateType tenv a
     goal (CheckJ ctx' normal_a m)
checkJ ctx (FunT :$: [a,b]) (Lam :$: [sc']) =
  do let (_, [n], m) = openScope (hypotheticalContext ctx) sc'
         ctx' = ctx { hypotheticalContext =
                        HasType n (instantiate0 a) : hypotheticalContext ctx
                    }
     goal (CheckJ ctx' (instantiate0 b) m)
checkJ ctx (ConT c :$: as) (Con c' :$: ms) =
  do (bscs, tc) <- termConstructorInContext ctx c'
     unless (tc == c)
       (failure
         (ElabError
           ("Term constructor `"
             ++ prettyQualifiedConstructor c'
             ++ "` constructs a term in the type `"
             ++ prettyQualifiedConstructor tc
             ++ "` but is being checked against `"
             ++ prettyQualifiedConstructor c)))
     unless (length bscs == length ms)
       (failure
         (ElabError
           ("Term constructor `"
             ++ prettyQualifiedConstructor c'
             ++ "` expects " ++ show (length bscs)
             ++ " arguments but was given " ++ show (length ms))))
     let as' = map instantiate0 as
         bs = map (\bsc -> instantiate bsc as') bscs
         tenv = nominalContextToTypeEnv ctx
         normal_bs = map (evaluateType tenv) bs
     forM_ (zip normal_bs ms) $ \(b,m) ->
       goal (CheckJ ctx b (instantiate0 m))
checkJ ctx t (Case :$: (m:clsscs)) =
  do a <- goal (SynthJ ctx (instantiate0 m))
     case a of
       ConT tc :$: bs ->
         do let cls = map instantiate0 clsscs
            noRepeatedConstructors cls
            coversAllConstructors ctx tc cls
            let tenv = nominalContextToTypeEnv ctx
                normal_bs = map (evaluateType tenv . instantiate0) bs 
            forM_ cls $ \cl ->
              goal (ClauseJ ctx tc normal_bs t cl)
       _ ->
         failure
           (ElabError
             ("Cannot case on non-constructed data `"
               ++ pretty (instantiate0 m) ++ "a"))
checkJ ctx (CompT :$: [a]) (Success :$: [m]) =
  goal (CheckJ ctx (instantiate0 a) (instantiate0 m))
checkJ _ (CompT :$: [_]) (Failure :$: []) =
  return ()
checkJ ctx a m =
  case (isType a, isTerm m) of
    (True,True) ->
      do a' <- synthJ ctx m
         let tenv = nominalContextToTypeEnv ctx
             normal_a = evaluateType tenv a
             normal_a' = evaluateType tenv a'
         goal (EqualJ ctx normal_a normal_a')
         return ()
    (True,False) ->
      failure
        (ElabError
          ("Cannot check the type of a type: `" ++ pretty m ++ "`"))
    (False,_) ->
      failure
        (ElabError
          ("Cannot check against a term: `" ++ pretty a ++ "`"))






synthJ :: Context -> Term -> Decomposer Term
synthJ ctx (Var (Free (FreeVar x))) =
  do t <- termVariableInHypotheticalContext (hypotheticalContext ctx) x
     let tenv = nominalContextToTypeEnv ctx
         normal_t = evaluateType tenv t
     return normal_t
synthJ _ (Var (Bound _ _)) =
  failure
    (ElabError
      ("Cannot synthesize the type of a bound term variable."))
synthJ ctx (Decname n :$: []) =
  do t <- termNameInContext ctx n
     let tenv = nominalContextToTypeEnv ctx
         normal_t = evaluateType tenv t
     return normal_t
synthJ ctx (Isa :$: [a,m]) =
  do let tenv = nominalContextToTypeEnv ctx
         normal_a = evaluateType tenv (instantiate0 a)
     goal (CheckJ ctx normal_a (instantiate0 m))
     return normal_a
synthJ ctx (Inst :$: [m,a]) =
  do b <- goal (SynthJ ctx (instantiate0 m))
     case b of
       ForallT k :$: [sc] ->
         do k' <- goal (IsTypeJ ctx (instantiate0 a))
            unless (k == k')
              (failure
                (ElabError
                  ("Term `" ++ pretty (instantiate0 m)
                    ++ "` expects a type of kind `"
                    ++ prettyKind k ++ "` but was given one of kind `"
                    ++ prettyKind k')))
            let tenv = nominalContextToTypeEnv ctx
            return (evaluateType tenv (instantiate sc [instantiate0 a]))
       _ -> failure
              (ElabError
                ("Cannot instantiate the term `" ++ pretty (instantiate0 m)
                  ++ "` which has non-quantified type `" ++ pretty b ++ "`"))
synthJ ctx (App :$: [m,n]) =
  do a <- goal (SynthJ ctx (instantiate0 m))
     case a of
       FunT :$: [b,c] ->
         do let tenv = nominalContextToTypeEnv ctx
                normal_b = evaluateType tenv (instantiate0 b)
            goal (CheckJ ctx normal_b (instantiate0 n))
            return (instantiate0 c)
       _ -> failure
              (ElabError
                ("Cannot apply the term `" ++ pretty (instantiate0 m)
                  ++ "` which has non-function type `" ++ pretty a ++ "`"))
synthJ _ (CompBuiltin n :$: []) =
  do t <- synthCompBuiltin n
     return (compTH t)
synthJ ctx m0@(Bind :$: [m,sc]) =
  do a <- goal (SynthJ ctx (instantiate0 m))
     case a of
       CompT :$: [b] ->
         do let (_, [n], m') = openScope (hypotheticalContext ctx) sc
                ctx' = ctx { hypotheticalContext =
                               HasType n (instantiate0 b)
                                 : hypotheticalContext ctx
                           }
            c <- goal (SynthJ ctx' m')
            case c of
              CompT :$: [_] ->
                return c
              _ -> failure
                     (ElabError
                       ("The term `" ++ pretty m0 ++ "` should have a clause"
                         ++ " that returns a computation type but instead"
                         ++ " has one that returns `" ++ pretty c ++ "`"))
       _ -> failure
              (ElabError
                ("Cannot bind the term `" ++ pretty (instantiate0 m)
                  ++ "` which has non-computation type `" ++ pretty a ++ "`"))
synthJ _ (PrimInteger _ :$: []) =
  return integerTH
synthJ _ (PrimFloat _ :$: []) =
  return floatTH
synthJ _ (PrimByteString _ :$: []) =
  return byteStringTH
synthJ ctx (Builtin n :$: ms) =
  do (as,b) <- signatureOfBuiltin n
     unless (length as == length ms)
       (failure
         (ElabError
           ("Builtin `" ++ n ++ "` expects " ++ show (length as)
             ++ " arguments but was given " ++ show (length ms))))
     let tenv = nominalContextToTypeEnv ctx
         normal_as = map (evaluateType tenv) as
     forM_ (zip normal_as ms) $ \(a,m) ->
       goal (CheckJ ctx a (instantiate0 m))
     return b
synthJ _ a =
  failure
    (ElabError
      ("Cannot synthesize the type of `" ++ pretty a ++ "`"))






clauseJ
  :: Context
  -> QualifiedConstructor
  -> [Term]
  -> Term
  -> Clause
  -> Decomposer ()
clauseJ ctx tc as t (Clause c :$: [sc]) =
  do (bscs, tc') <- termConstructorInContext ctx c
     unless (tc == tc')
       (failure
         (ElabError
           ("Term constructor `"
             ++ prettyQualifiedConstructor c
             ++ "` constructs a term in the type `"
             ++ prettyQualifiedConstructor tc
             ++ "` but is being checked against `"
             ++ prettyQualifiedConstructor tc')))
     unless (length bscs == length (names sc))
       (failure
         (ElabError
           ("Term constructor `"
             ++ prettyQualifiedConstructor c
             ++ "` expects " ++ show (length bscs)
             ++ " arguments but was given " ++ show (length (names sc)))))
     let (_, ns, m) = openScope (hypotheticalContext ctx) sc
         bs = map (\bsc -> instantiate bsc as) bscs
         tenv = nominalContextToTypeEnv ctx
         normal_bs = map (evaluateType tenv) bs
         ctx' = ctx { hypotheticalContext =
                        [ HasType n b | (n,b) <- zip ns normal_bs ]
                          ++ hypotheticalContext ctx
                    }
     goal (CheckJ ctx' t m)
clauseJ _ _ _ _ _ =
  error "Tried to check that a non-clause is a well-formed clause.\
        \ This should be impossible."





equalJ :: Context -> Term -> Term -> Decomposer ()
equalJ _ (Var x) (Var y) =
  if x == y
    then return ()
    else failure
           (ElabError
             ("Variables not equal: `"
               ++ name x
               ++ "` and `"
               ++ name y
               ++ "`"))
equalJ ctx@(Context l ls' nomctx _) m0@(c :$: scs) m0'@(c' :$: scs') =
  if c /= c'
  then failure
         (ElabError
           ("Terms not equal: `"
             ++ pretty m0
             ++ "` and `"
             ++ pretty m0'
             ++ "`"))
  else forM_ (zip scs scs') $ \(sc,sc') ->
         do let (xs, ns, m) = openScope (hypotheticalContext ctx) sc
                m' = instantiate sc' (map (Var . Free) xs)
                tenv = nominalContextToTypeEnv (Context l ls' nomctx [])
                normal_m = evaluateType tenv m
                normal_m' = evaluateType tenv m'
                ctx' = ctx { hypotheticalContext =
                               [ HasType n undefined | n <- ns ]
                                 ++ hypotheticalContext ctx
                           }
            goal (EqualJ ctx' normal_m normal_m')
equalJ _ m m' =
  failure
    (ElabError
      ("Terms not equal: `" ++ pretty m ++ "` and `" ++ pretty m' ++ "`"))




equalAllJ :: Context -> Term -> [Term] -> Decomposer ()
equalAllJ _ _ [] = return ()
equalAllJ ctx a (b:bs) =
  do goal (EqualJ ctx a b)
     goal (EqualAllJ ctx a bs)