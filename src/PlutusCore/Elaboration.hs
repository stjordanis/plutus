{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}







module PlutusCore.Elaboration where

import Utils.ABT
import Utils.Elaborator hiding (openScope)
import Utils.Names
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
import Control.Monad.State
import Data.Functor.Identity
import Data.List
import Data.Maybe (isJust)

import Debug







instance Decomposable () ElabError Judgment where
  decompose (ElabProgramJ prog) = programJ prog
  decompose (ElabModuleJ ctx mdl) = moduleJ ctx mdl
  decompose (ElabDeclJ l ls' nomctx decl) =
    declJ l ls' nomctx decl
  decompose (ElabAltJ l ls' nomctx alt tc ksigs) =
    altJ l ls' nomctx alt tc ksigs
  decompose (IsTypeJ ctx a) = isTypeJ ctx a
  decompose (IsTypeValueJ a) = isTypeValueJ a
  decompose (IsTermValueJ m) = isTermValueJ m
  decompose (CheckJ ctx a m) = checkJ ctx a m
  decompose (SynthJ ctx m) = synthJ ctx m
  decompose (ClauseJ ctx tc as cl) = clauseJ ctx tc as cl
  decompose (EqualJ ctx a b) = equalJ ctx a b
  decompose (EqualAllJ ctx a bs) = equalAllJ ctx a bs








openScope :: HypotheticalContext -> Scope TermF -> ([FreeVar], [String], Term)
openScope ctx sc =
  let ns = names sc
      oldNs = map variableName ctx
      freshNs = map FreeVar (freshen oldNs ns)
      newVars = [ Var (Free n) | n <- freshNs ]
      newNames = [ x | FreeVar x <- freshNs ]
      m = instantiate sc newVars
  in (freshNs, newNames, m)








nominalContextToTypeEnv :: NominalContext -> QualifiedEnv
nominalContextToTypeEnv [] = []
nominalContextToTypeEnv (TypeJ l nm u _ : nomctx) =
  (QualifiedName l nm, u) : nominalContextToTypeEnv nomctx
nominalContextToTypeEnv (_ : nomctx) =
  nominalContextToTypeEnv nomctx






freshModuleName :: NominalContext -> String -> Decomposer ()
freshModuleName [] _ = return ()
freshModuleName (ModJ l' : _) l | l == l' =
  failure
    (ElabError
      ("The module name " ++ l ++ " is already in used"))
freshModuleName (_ : nomctx) l = freshModuleName nomctx l





freshTypeConstructor
  :: String -> NominalContext -> String -> Decomposer ()
freshTypeConstructor _ [] _ = return ()
freshTypeConstructor l (TyConJ l' tcn' _ : _) tcn | l == l' && tcn == tcn' =
  failure
    (ElabError
      ("The data type " ++ tcn
        ++ " has already been declared in the module " ++ l))
freshTypeConstructor l (_ : nomctx) tcn =
  freshTypeConstructor l nomctx tcn






freshTypeName :: String -> NominalContext -> String -> Decomposer ()
freshTypeName _ [] _ = return ()
freshTypeName l (TypeJ l' tnm' _ _ : _) tnm | l == l' && tnm == tnm' =
  failure
    (ElabError
      ("The type name " ++ tnm
        ++ " has already been declared in the module " ++ l))
freshTypeName l (_ : nomctx) tnm =
  freshTypeName l nomctx tnm 






freshTermConstructor
  :: NominalContext -> QualifiedConstructor -> String -> Decomposer ()
freshTermConstructor [] _ _ = return ()
freshTermConstructor (ConJ l cn _ tcn : _) (QualifiedConstructor l' tcn') cn'
  | l == l' && cn == cn' && tcn == tcn' =
      failure
           (ElabError
             ("Data type "
               ++ prettyQualifiedConstructor (QualifiedConstructor l' tcn')
               ++ " already declares a constructor named " ++ cn))
freshTermConstructor (_ : nomctx) tc cn = freshTermConstructor nomctx tc cn






freshTermName :: String -> NominalContext -> String -> Decomposer ()
freshTermName _ [] _ = return ()
freshTermName l (TermJ l' nm' _ : _) nm | l == l' && nm == nm' =
  failure
    (ElabError
      ("The term name " ++ nm
        ++ " has already been declared in the module " ++ l))
freshTermName l (_ : nomctx) nm =
  freshTermName l nomctx nm






undefinedTermName :: String -> NominalContext -> String -> Decomposer ()
undefinedTermName _ [] _ = return ()
undefinedTermName l (DefJ l' nm' _ : _) nm | l == l' && nm == nm' =
  failure
    (ElabError
      ("The term name " ++ nm
        ++ " has already been defined in the module " ++ l))
undefinedTermName l (_ : nomctx) nm =
  undefinedTermName l nomctx nm







typeNameInContext
  :: Context -> QualifiedName -> Decomposer Kind
typeNameInContext ctx n@(QualifiedName l nm) =
  case find findKind (nominalContext ctx) of
    Just (TypeJ _ _ _ k)
      |  l == currentModule ctx
      || any findExp (nominalContext ctx) ->
        return k
    _ -> failure
           (ElabError
             ("Type name not in scope: " ++ prettyQualifiedName n))
  where
    findKind (TypeJ l' nm' _ _) = l' == l && nm' == nm
    findKind _ = False
    
    findExp (ExpTypeJ l' nm') = l' == l && nm' == nm
    findExp _ = False





typeConstructorInContext
  :: Context -> QualifiedConstructor -> Decomposer [Kind]
typeConstructorInContext ctx c@(QualifiedConstructor l cn) =
  case find findKind (nominalContext ctx) of
    Just (TyConJ _ _ ks)
      |  l == currentModule ctx
      || any findExp (nominalContext ctx) ->
        return ks
    _ -> failure
           (ElabError
             ("Type constructor not in scope: "
               ++ prettyQualifiedConstructor c))
  where
    findKind (TyConJ l' cn' _) = l' == l && cn' == cn
    findKind _ = False
    
    findExp (ExpTypeJ l' cn') = l' == l && cn' == cn
    findExp _ = False




termConstructorInContext
  :: Context
  -> QualifiedConstructor
  -> Decomposer ([Scope TermF], QualifiedConstructor)
termConstructorInContext ctx c@(QualifiedConstructor l cn) =
  case find findSig (nominalContext ctx) of
    Just (ConJ _ _ ascs tcn)
      |  l == currentModule ctx
      || any findExp (nominalContext ctx) ->
        return (ascs, QualifiedConstructor l tcn)
    _ -> failure
           (ElabError
             ("Term constructor not in scope: "
               ++ prettyQualifiedConstructor c))
  where
    findSig (ConJ l' cn' _ _) = l' == l && cn' == cn
    findSig _ = False
    
    findExp (ExpTermJ l' cn') = l' == l && cn' == cn
    findExp _ = False






termNameInContext
  :: Context -> QualifiedName -> Decomposer Term
termNameInContext ctx n@(QualifiedName l nm) =
  case find findType (nominalContext ctx) of
    Just (TermJ _ _ u)
      |  l == currentModule ctx
      || any findExp (nominalContext ctx) ->
        return u
    _ -> failure
           (ElabError
             ("Term name not in scope: "
               ++ prettyQualifiedName n))
  where
    findType (TermJ l' nm' _) = l' == l && nm' == nm
    findType _ = False
    
    findExp (ExpTermJ l' nm') = l' == l && nm' == nm
    findExp _ = False






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
  do let cs = [ c | Clause c _ <- cls ]
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






coversAllConstructors :: NominalContext
                      -> QualifiedConstructor
                      -> [Clause]
                      -> Decomposer ()
coversAllConstructors nomctx tc cls =
  do let cs = [ QualifiedConstructor l cn
              | ConJ l cn _ tcn <- nomctx
              , tc == QualifiedConstructor l tcn
              ]
         missing = cs \\ [ c | Clause c _ <- cls ]
     unless (null missing)
       (failure
         (ElabError
           ("The constructors "
             ++ unwords [ "`" ++ prettyQualifiedConstructor c ++ "`"
                        | c <- missing
                        ]
             ++ " are missing clauses in a case term")))






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
           , conTH (QualifiedConstructor "Prelude" "Bool") []
           ))
      , ("lessThanEqualsInteger"
        , ( [integerTH, integerTH]
          , conTH (QualifiedConstructor "Prelude" "Bool") []
          ))
      , ("greaterThanInteger"
        , ( [integerTH, integerTH]
          , conTH (QualifiedConstructor "Prelude" "Bool") []
          ))
      , ("greaterThanEqualsInteger"
        , ( [integerTH, integerTH]
          , conTH (QualifiedConstructor "Prelude" "Bool") []
          ))
      , ("equalsInteger"
        ,  ( [integerTH, integerTH]
           , conTH (QualifiedConstructor "Prelude" "Bool") []
           ))
      , ("integerToFloat", ([integerTH], floatTH))
      , ("integerToByteString", ([integerTH], byteStringTH))
      
      
      , ("addFloat", ([floatTH, floatTH], floatTH))
      , ("subtractFloat", ([floatTH, floatTH], floatTH))
      , ("multiplyFloat", ([floatTH, floatTH], floatTH))
      , ("divideFloat", ([floatTH, floatTH], floatTH))
      , ("lessThanFloat"
        ,  ( [floatTH, floatTH]
           , conTH (QualifiedConstructor "Prelude" "Bool") []
           ))
      , ("lessThanEqualsFloat"
        , ( [floatTH, floatTH]
          , conTH (QualifiedConstructor "Prelude" "Bool") []
          ))
      , ("greaterThanFloat"
        , ( [floatTH, floatTH]
          , conTH (QualifiedConstructor "Prelude" "Bool") []
          ))
      , ("greaterThanEqualsFloat"
        , ( [floatTH, floatTH]
          , conTH (QualifiedConstructor "Prelude" "Bool") []
          ))
      , ("equalsFloat"
        ,  ( [floatTH, floatTH]
           , conTH (QualifiedConstructor "Prelude" "Bool") []
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
           , conTH (QualifiedConstructor "Prelude" "Bool") []
           ))
      ]







programJ :: Program -> Decomposer NominalContext
programJ (Program modules) =
  foldAccumLM
    (\nomctx mdl -> goal (ElabModuleJ nomctx mdl))
    modules





moduleJ :: NominalContext -> Module -> Decomposer NominalContext
moduleJ nomctx (Module l ls' (Exports tyexp tmexp) decls) =
  do freshModuleName nomctx l
     nomctx' <- foldAccumLM
       (\nomctx'' decl -> goal (ElabDeclJ l ls' nomctx'' decl))
       decls
     return (nomctx'
               ++ (tyexp >>= typeExportToNominalContext)
               ++ termExportNominalContext)
  where
    typeExportToNominalContext :: TypeExport -> NominalContext
    typeExportToNominalContext (TypeNameExport nm) =
      [ ExpTypeJ l nm ]
    typeExportToNominalContext (TypeConstructorExport tcn cns) =
      ExpTypeJ l tcn : [ ExpTermJ l cn | cn <- cns ]
    
    termExportNominalContext :: NominalContext
    termExportNominalContext = [ ExpTermJ l nm | nm <- tmexp ]





declJ :: String
      -> [String]
      -> NominalContext
      -> Declaration
      -> Decomposer NominalContext
declJ l ls' nomctx (DataDeclaration tcn ksigs alts) =
  do freshTypeConstructor l nomctx tcn
     let nomctxAddition = TyConJ l tcn [ k | KindSig _ k <- ksigs ]
     nomctxs' <- forM alts $ \alt ->
       goal (ElabAltJ
              l
              ls'
              (nomctxAddition : nomctx)
              alt
              (QualifiedConstructor l tcn)
              ksigs)
     return (nomctxAddition : concat nomctxs')
declJ l ls' nomctx (TypeDeclaration tnm u) =
  do freshTypeName l nomctx tnm
     goal (IsTypeValueJ u)
     k <- goal (IsTypeJ (Context l ls' nomctx []) u)
     return [ TypeJ l tnm u k ]
declJ l ls' nomctx (TermDeclaration nm u) =
  do freshTermName l nomctx nm
     goal (IsTypeValueJ u)
     k <- goal (IsTypeJ (Context l ls' nomctx []) u)
     unless (k == TypeK)
       (failure
         (ElabError
           ("Cannot declare a term to have the type `"
             ++ pretty u
             ++ "` because it is of kind `"
             ++ prettyKind k
             ++ "` rather than of kind `"
             ++ prettyKind TypeK
             ++ "`")))
     return [ TermJ l nm u ]
declJ l ls' nomctx (TermDefinition nm v) =
  do undefinedTermName l nomctx nm
     u <- termNameInContext
            (Context l ls' nomctx [])
            (QualifiedName l nm)
     goal (IsTermValueJ v)
     goal (CheckJ (Context l ls' nomctx []) u v)
     return [ DefJ l nm v ]





altJ :: String
     -> [String]
     -> NominalContext
     -> Alt
     -> QualifiedConstructor
     -> [KindSig]
     -> Decomposer NominalContext
altJ l ls' nomctx (Alt cn ascs) tc@(QualifiedConstructor l' tcn) ksigs =
  do unless (l == l')
       (failure
         (ElabError
           ("Cannot declare a new constructor for "
             ++ prettyQualifiedConstructor tc
             ++ " in the module "
             ++ l
             ++ " which is not where it was declared")))
     freshTermConstructor nomctx tc cn
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
     return [ConJ l cn ascs tcn]







isTypeJ :: Context -> Term -> Decomposer Kind
isTypeJ ctx (Var (Free (FreeVar x))) =
  typeVariableInHypotheticalContext (hypotheticalContext ctx) x
isTypeJ _ (Var (Bound _ _)) =
  failure
    (ElabError
      ("Cannot synthesize the kind of a bound type variable."))
isTypeJ ctx (In (DecnameT n)) =
  typeNameInContext ctx n
isTypeJ ctx (In (FunT a b)) =
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
isTypeJ ctx (In (ConT c as)) =
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
isTypeJ ctx (In (CompT a)) =
  do k <- goal (IsTypeJ ctx (instantiate0 a))
     unless (k == TypeK)
       (failure
         (ElabError
           ("Kind of " ++ pretty (instantiate0 a)
             ++ " should be (type) but is actually "
             ++ prettyKind k)))
     return TypeK
isTypeJ ctx (In (ForallT k sc)) =
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
isTypeJ _ (In IntegerT) =
  return TypeK
isTypeJ _ (In FloatT) =
  return TypeK
isTypeJ _ (In ByteStringT) =
  return TypeK
isTypeJ ctx (In (LamT k sc)) =
  do let (_, [n], a) = openScope (hypotheticalContext ctx) sc
         ctx' = ctx { hypotheticalContext =
                        HasKind n k : hypotheticalContext ctx
                    }
     k' <- goal (IsTypeJ ctx' a)
     return (FunK k k')
isTypeJ ctx (In (AppT a b)) =
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
isTypeValueJ (In (FunT a b)) =
  do goal (IsTypeValueJ (instantiate0 a))
     goal (IsTypeValueJ (instantiate0 b))
isTypeValueJ (In (ConT _ as)) =
  forM_ as $ \a ->
    goal (IsTypeValueJ (instantiate0 a))
isTypeValueJ (In (CompT a)) =
  goal (IsTypeValueJ (instantiate0 a))
isTypeValueJ (In (LamT _ _)) =
  return ()
isTypeValueJ (In (ForallT _ _)) =
  return ()
isTypeValueJ (In IntegerT) =
  return ()
isTypeValueJ (In FloatT) =
  return ()
isTypeValueJ (In ByteStringT) =
  return ()
isTypeValueJ a =
  failure
    (ElabError
      ("The type `" ++ pretty a ++ "` is not a value"))






isTermValueJ :: Term -> Decomposer ()
isTermValueJ (In (Abst _)) =
  return ()
isTermValueJ (In (Lam _)) =
  return ()
isTermValueJ (In (Con _ ms)) =
  forM_ ms $ \m ->
    goal (IsTermValueJ (instantiate0 m))
isTermValueJ (In (Success m)) =
  goal (IsTermValueJ (instantiate0 m))
isTermValueJ (In Failure) =
  return ()
isTermValueJ (In TxHash) =
  return ()
isTermValueJ (In BlockNum) =
  return ()
isTermValueJ (In BlockTime) =
  return ()
isTermValueJ (In (Bind m _)) =
  goal (IsTermValueJ (instantiate0 m))
isTermValueJ m =
  failure
    (ElabError
      ("The term `" ++ pretty m ++ "` is not a value"))






checkJ :: Context -> Term -> Term -> Decomposer ()
checkJ ctx (In (ForallT k sc)) (In (Abst sc')) =
  do let ([x], [n], a) = openScope (hypotheticalContext ctx) sc
         ctx' = ctx { hypotheticalContext =
                        HasKind n k : hypotheticalContext ctx
                    }
         m = instantiate sc' [Var (Free x)]
     goal (CheckJ ctx' a m)
checkJ ctx (In (FunT a b)) (In (Lam sc')) =
  do let (_, [n], m) = openScope (hypotheticalContext ctx) sc'
         ctx' = ctx { hypotheticalContext =
                        HasType n (instantiate0 a) : hypotheticalContext ctx
                    }
     goal (CheckJ ctx' (instantiate0 b) m)
checkJ ctx (In (ConT c as)) (In (Con c' ms)) =
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
         tenv = nominalContextToTypeEnv (nominalContext ctx)
         normal_bs = map (evaluateType tenv) bs
     forM_ (zip normal_bs ms) $ \(b,m) ->
       goal (CheckJ ctx b (instantiate0 m))
checkJ ctx (In (CompT a)) (In (Success m)) =
  goal (CheckJ ctx (instantiate0 a) (instantiate0 m))
checkJ _ (In (CompT _)) (In Failure) =
  return ()
checkJ ctx a m =
  case (isType a, isTerm m) of
    (True,True) ->
      do a' <- synthJ ctx m
         goal (EqualJ ctx a a')
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
  termVariableInHypotheticalContext (hypotheticalContext ctx) x
synthJ _ (Var (Bound _ _)) =
  failure
    (ElabError
      ("Cannot synthesize the type of a bound term variable."))
synthJ ctx (In (Decname n)) =
  termNameInContext ctx n
synthJ ctx (In (Isa m a)) =
  do let tenv = nominalContextToTypeEnv (nominalContext ctx)
         normal_a = evaluateType tenv (instantiate0 a)
     goal (CheckJ ctx normal_a (instantiate0 m))
     return normal_a
synthJ ctx (In (Inst m a)) =
  do b <- goal (SynthJ ctx (instantiate0 m))
     case b of
       In (ForallT k sc) ->
         do k' <- goal (IsTypeJ ctx (instantiate0 a))
            unless (k == k')
              (failure
                (ElabError
                  ("Term `" ++ pretty (instantiate0 m)
                    ++ "` expects a type of kind `"
                    ++ prettyKind k ++ "` but was given one of kind `"
                    ++ prettyKind k')))
            let tenv = nominalContextToTypeEnv (nominalContext ctx)
            return (evaluateType tenv (instantiate sc [instantiate0 a]))
       _ -> failure
              (ElabError
                ("Cannot instantiate the term `" ++ pretty (instantiate0 m)
                  ++ "` which has non-quantified type `" ++ pretty b ++ "`"))
synthJ ctx (In (App m n)) =
  do a <- goal (SynthJ ctx (instantiate0 m))
     case a of
       In (FunT b c) ->
         do goal (CheckJ ctx (instantiate0 b) (instantiate0 n))
            return (instantiate0 c)
       _ -> failure
              (ElabError
                ("Cannot apply the term `" ++ pretty (instantiate0 m)
                  ++ "` which has non-function type `" ++ pretty a ++ "`"))
synthJ ctx (In (Case m cls)) =
  do a <- goal (SynthJ ctx (instantiate0 m))
     case a of
       In (ConT tc bs) ->
         do noRepeatedConstructors cls
            coversAllConstructors (nominalContext ctx) tc cls
            let bs' = map instantiate0 bs
            cs <- forM cls $ \cl ->
              goal (ClauseJ ctx tc bs' cl)
            case cs of
              [] ->
                failure
                  (ElabError
                    "Cannot synthesize the type of an empty case term")
              c:cs' ->
                do goal (EqualAllJ ctx c cs')
                   return c
       _ ->
         failure
           (ElabError
             ("Cannot case on non-constructed data `"
               ++ pretty (instantiate0 m) ++ "a"))
synthJ _ (In TxHash) =
  return (compTH byteStringTH)
synthJ _ (In BlockNum) =
  return (compTH integerTH)
synthJ _ (In BlockTime) =
  return (compTH (conTH (QualifiedConstructor "Prelude" "DateTime") []))
synthJ ctx m0@(In (Bind m sc)) =
  do a <- goal (SynthJ ctx (instantiate0 m))
     case a of
       In (CompT b) ->
         do let (_, [n], m') = openScope (hypotheticalContext ctx) sc
                ctx' = ctx { hypotheticalContext =
                               HasType n (instantiate0 b)
                                 : hypotheticalContext ctx
                           }
            c <- goal (SynthJ ctx' m')
            case c of
              In (CompT _) ->
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
synthJ _ (In (PrimInteger _)) =
  return integerTH
synthJ _ (In (PrimFloat _)) =
  return floatTH
synthJ _ (In (PrimByteString _)) =
  return byteStringTH
synthJ ctx (In (Builtin n ms)) =
  do (as,b) <- signatureOfBuiltin n
     unless (length as == length ms)
       (failure
         (ElabError
           ("Builtin `" ++ n ++ "` expects " ++ show (length as)
             ++ " arguments but was given " ++ show (length ms))))
     forM_ (zip as ms) $ \(a,m) ->
       goal (CheckJ ctx a (instantiate0 m))
     return b
synthJ _ a =
  failure
    (ElabError
      ("Cannot synthesize the type of `" ++ pretty a ++ "`"))





clauseJ
  :: Context -> QualifiedConstructor -> [Term] -> Clause -> Decomposer Term
clauseJ ctx tc as (Clause c sc) =
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
         tenv = nominalContextToTypeEnv (nominalContext ctx)
         normal_bs = map (evaluateType tenv) bs
         ctx' = ctx { hypotheticalContext =
                        [ HasType n b | (n,b) <- zip ns normal_bs ]
                          ++ hypotheticalContext ctx
                    }
     goal (SynthJ ctx' m)





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
equalJ _ (In (Decname n)) (In (Decname n')) =
  if n == n'
    then return ()
    else failure
           (ElabError
             ("Qualified names not equal: `"
               ++ prettyQualifiedName n
               ++ "` and `"
               ++ prettyQualifiedName n'
               ++ "`"))
equalJ ctx (In (Isa m a)) (In (Isa m' a')) =
  do goal (EqualJ ctx (instantiate0 m) (instantiate0 m'))
     goal (EqualJ ctx (instantiate0 a) (instantiate0 a'))
equalJ ctx (In (Abst sc)) (In (Abst sc')) =
  do let ([x], [n], a) = openScope (hypotheticalContext ctx) sc
         a' = instantiate sc' [Var (Free x)]
         ctx' = ctx { hypotheticalContext =
                        HasKind n undefined : hypotheticalContext ctx
                    }
     goal (EqualJ ctx' a a')
equalJ ctx (In (Inst m a)) (In (Inst m' a')) =
  do goal (EqualJ ctx (instantiate0 m) (instantiate0 m'))
     goal (EqualJ ctx (instantiate0 a) (instantiate0 a'))
equalJ ctx (In (Lam sc)) (In (Lam sc')) =
  do let ([x], [n], m) = openScope (hypotheticalContext ctx) sc
         m' = instantiate sc' [Var (Free x)]
         ctx' = ctx { hypotheticalContext =
                        HasType n undefined : hypotheticalContext ctx
                    }
     goal (EqualJ ctx' m m')
equalJ ctx (In (App m n)) (In (App m' n')) =
  do goal (EqualJ ctx (instantiate0 m) (instantiate0 m'))
     goal (EqualJ ctx (instantiate0 n) (instantiate0 n'))
equalJ ctx (In (Con c ms)) (In (Con c' ms')) =
  do unless (c == c')
       (failure
         (ElabError
           ("Qualified constructors not equal: `"
             ++ prettyQualifiedConstructor c
             ++ "` and `"
             ++ prettyQualifiedConstructor c'
             ++ "`")))
     forM_ (zip ms ms') $ \(m,m') ->
       goal (EqualJ ctx (instantiate0 m) (instantiate0 m'))
equalJ ctx (In (Case m cls)) (In (Case m' cls')) =
  do goal (EqualJ ctx (instantiate0 m) (instantiate0 m'))
     unless (length cls == length cls')
       (failure
         (ElabError
           ("Different number of clauses: "
             ++ show (length cls)
             ++ " and "
             ++ show (length cls'))))
     forM_ (zip cls cls') $ \(Clause c sc, Clause c' sc') ->
       do unless (c == c')
            (failure
              (ElabError
                ("Qualified constructors not equal: `"
                  ++ prettyQualifiedConstructor c
                  ++ "` and `"
                  ++ prettyQualifiedConstructor c'
                  ++ "`")))
          let (xs, ns, m'') = openScope (hypotheticalContext ctx) sc
              m''' = instantiate sc' (map (Var . Free) xs)
              ctx' = ctx { hypotheticalContext =
                             [ HasType n undefined | n <- ns ]
                               ++ hypotheticalContext ctx
                         }
          goal (EqualJ ctx' m'' m''')
equalJ ctx (In (Success m)) (In (Success m')) =
  goal (EqualJ ctx (instantiate0 m) (instantiate0 m'))
equalJ _ (In Failure) (In Failure) =
  return ()
equalJ _ (In TxHash) (In TxHash) =
  return ()
equalJ _ (In BlockNum) (In BlockNum) =
  return ()
equalJ _ (In BlockTime) (In BlockTime) =
  return ()
equalJ ctx (In (Bind m sc)) (In (Bind m' sc')) =
  do goal (EqualJ ctx (instantiate0 m) (instantiate0 m'))
     let ([x],[n],m'') = openScope (hypotheticalContext ctx) sc
         m''' = instantiate sc' [Var (Free x)]
         ctx' = ctx { hypotheticalContext =
                        HasType n undefined : hypotheticalContext ctx
                    }
     goal (EqualJ ctx' m'' m''')
equalJ _ (In (PrimInteger n)) (In (PrimInteger n')) =
  unless (n == n')
    (failure
      (ElabError
        ("Integers not equal: `"
          ++ show n
          ++ "` and `"
          ++ show n'
          ++ "`")))
equalJ _ (In (PrimFloat f)) (In (PrimFloat f')) =
  unless (f == f')
    (failure
      (ElabError
        ("Floats not equal: `"
          ++ show f
          ++ "` and `"
          ++ show f'
          ++ "`")))
equalJ _ (In (PrimByteString bs)) (In (PrimByteString bs')) =
  unless (bs == bs')
    (failure
      (ElabError
        ("Bytestrings not equal: `"
          ++ show bs
          ++ "` and `"
          ++ show bs'
          ++ "`")))
equalJ ctx (In (Builtin n ms)) (In (Builtin n' ms')) =
  do unless (n == n')
       (failure
         (ElabError
           ("Builtins not equal: `"
             ++ show n
             ++ "` and `"
             ++ show n'
             ++ "`")))
     forM_ (zip ms ms') $ \(m,m') ->
       goal (EqualJ ctx (instantiate0 m) (instantiate0 m'))
equalJ _ (In (DecnameT n)) (In (DecnameT n')) =
  if n == n'
    then return ()
    else failure
           (ElabError
             ("Qualified names not equal: `"
               ++ prettyQualifiedName n
               ++ "` and `"
               ++ prettyQualifiedName n'
               ++ "`"))
equalJ ctx (In (FunT a b)) (In (FunT a' b')) =
  do goal (EqualJ ctx (instantiate0 a) (instantiate0 a'))
     goal (EqualJ ctx (instantiate0 b) (instantiate0 b'))
equalJ ctx (In (ConT c as)) (In (ConT c' as')) =
  do unless (c == c')
       (failure
         (ElabError
           ("Qualified constructors not equal: `"
             ++ prettyQualifiedConstructor c
             ++ "` and `"
             ++ prettyQualifiedConstructor c'
             ++ "`")))
     forM_ (zip as as') $ \(a,a') ->
       goal (EqualJ ctx (instantiate0 a) (instantiate0 a'))
equalJ ctx (In (CompT a)) (In (CompT a')) =
  goal (EqualJ ctx (instantiate0 a) (instantiate0 a'))
equalJ ctx (In (ForallT k sc)) (In (ForallT k' sc')) =
  do unless (k == k')
       (failure
         (ElabError
           ("Kinds not equal: `"
             ++ prettyKind k
             ++ "` and `"
             ++ prettyKind k'
             ++ "`")))
     let ([x],[n],a) = openScope (hypotheticalContext ctx) sc
         a' = instantiate sc' [Var (Free x)]
         ctx' = ctx { hypotheticalContext =
                        HasKind n undefined : hypotheticalContext ctx
                    }
     goal (EqualJ ctx' a a')
equalJ _ (In IntegerT) (In IntegerT) =
  return ()
equalJ _ (In FloatT) (In FloatT) =
  return ()
equalJ _ (In ByteStringT) (In ByteStringT) =
  return ()
equalJ ctx (In (LamT k sc)) (In (LamT k' sc')) =
  do unless (k == k')
       (failure
         (ElabError
           ("Kinds not equal: `"
             ++ prettyKind k
             ++ "` and `"
             ++ prettyKind k'
             ++ "`")))
     let ([x],[n],a) = openScope (hypotheticalContext ctx) sc
         a' = instantiate sc' [Var (Free x)]
         ctx' = ctx { hypotheticalContext =
                        HasKind n undefined : hypotheticalContext ctx
                    }
     goal (EqualJ ctx' a a')
equalJ ctx (In (AppT a b)) (In (AppT a' b')) =
  do goal (EqualJ ctx (instantiate0 a) (instantiate0 a'))
     goal (EqualJ ctx (instantiate0 b) (instantiate0 b'))
equalJ _ m m' =
  failure
    (ElabError
      ("Cannot equate `" ++ pretty m ++ "` and `" ++ pretty m' ++ "`"))




equalAllJ :: Context -> Term -> [Term] -> Decomposer ()
equalAllJ _ _ [] = return ()
equalAllJ ctx a (b:bs) =
  do goal (EqualJ ctx a b)
     goal (EqualAllJ ctx a bs)