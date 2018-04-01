{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}







module PlutusCore.Elaboration where

import Utils.ABT
--import Utils.Elaborator hiding (openScope)
--import Utils.Names
import Utils.Pretty
import Utils.ProofDev
--import Utils.Unifier
import Utils.Vars
import PlutusCore.ElabError
import PlutusCore.Evaluation
import PlutusCore.LanguageOptions
import PlutusCore.Term
import PlutusCore.Program
import PlutusCore.Contexts
import PlutusCore.Elaborator
import PlutusCore.Judgments
import PlutusCore.EvaluatorTypes

import Control.Monad.Except
import Control.Monad.State
--import Data.Functor.Identity
import Data.List
--import Data.Maybe (isJust)

--import Debug







instance Decomposable ElabState ElabError Judgment where
  decompose (ElabProgramJ prog) = programJ prog
  decompose (ElabDeclJ nomctx decl) =
    declJ nomctx decl
  decompose (ElabAltJ nomctx alt ksigs) =
    altJ nomctx alt ksigs
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








nominalContextToTypeEnv :: Context -> Environment
nominalContextToTypeEnv (Context { nominalContext = ds }) =
  ds >>= declarationToTypeEnv
  where
    declarationToTypeEnv :: Declaration -> Environment
    declarationToTypeEnv (TypeDeclaration n t) = [(n, t)]
    declarationToTypeEnv _ = []






freshTypeConstructor :: [Declaration] -> String -> ElabDecomposer ()
freshTypeConstructor ds n =
  unless (all freshInDeclaration ds)
    (failure
      (TypeConstructorAlreadyDeclared n))
  where
    freshInDeclaration :: Declaration -> Bool
    freshInDeclaration (DataDeclaration c _ _) = n /= c
    freshInDeclaration _ = True






freshTypeName :: [Declaration] -> String -> ElabDecomposer ()
freshTypeName ds n =
  unless (all freshInDeclaration ds)
    (failure
      (TypeNameAlreadyDeclared n))
  where
    freshInDeclaration :: Declaration -> Bool
    freshInDeclaration (TypeDeclaration n' _) = n /= n'
    freshInDeclaration _ = True






freshTermConstructor :: [Declaration] -> String -> ElabDecomposer ()
freshTermConstructor ds n =
  unless (all freshInDeclaration ds)
    (failure
      (TermConstructorAlreadyDeclared n))
  where
    freshInDeclaration :: Declaration -> Bool
    freshInDeclaration (DataDeclaration _ _ alts) =
      all freshInAlt alts
    freshInDeclaration _ = True
    
    freshInAlt :: Alt -> Bool
    freshInAlt (Alt n' _) = n /= n'






freshTermName :: [Declaration] -> String -> ElabDecomposer ()
freshTermName ds nm =
  unless (all freshInDeclaration ds)
    (failure
      (TermNameAlreadyDeclared nm))
  where
    freshInDeclaration :: Declaration -> Bool
    freshInDeclaration (TermDeclaration nm' _) = nm /= nm'
    freshInDeclaration _ = True






undefinedTermName :: [Declaration] -> String -> ElabDecomposer ()
undefinedTermName ds n =
  unless (all undefinedInDeclaration ds)
    (failure
      (TermNameAlreadyDefined n))
  where
    undefinedInDeclaration :: Declaration -> Bool
    undefinedInDeclaration (TermDefinition n' _ ) = n /= n'
    undefinedInDeclaration _ = True







typeNameInContext
  :: Context -> String -> ElabDecomposer Kind
typeNameInContext ctx@(Context { nominalContext = ds })
                  nm =
  
  findInDeclarations ds
  
  where
    findInDeclarations [] = failure (TypeNameNotInScope nm)
    findInDeclarations (TypeDeclaration nm' t:ds')
      | nm == nm' = goal (IsTypeJ ctx t)
      | otherwise = findInDeclarations ds'
    findInDeclarations (_:ds') = findInDeclarations ds'





typeConstructorInContext
  :: Context -> String -> ElabDecomposer [Kind]
typeConstructorInContext (Context { nominalContext = ds})
                         nm =
  findInDeclarations ds
  
  where
    findInDeclarations [] = failure (TypeConstructorNotInScope nm)
    findInDeclarations (DataDeclaration nm' ksigs _:ds')
      | nm == nm' = return [ k | KindSig _ k <- ksigs ]
      | otherwise = findInDeclarations ds'
    findInDeclarations (_:ds') = findInDeclarations ds'



termConstructorInContext
  :: Context
  -> String
  -> ElabDecomposer ([Scope PlutusSig], String)
termConstructorInContext (Context { nominalContext = ds })
                         nm =
  findInDeclarations ds
  
  where
    findInDeclarations [] = failure (TermConstructorNotInScope nm)
    findInDeclarations (DataDeclaration nm' _ alts:ds') =
      case findAlt alts of
        Nothing -> findInDeclarations ds'
        Just ascs -> return (ascs, nm')
    findInDeclarations (_:ds') = findInDeclarations ds'
    
    findAlt [] = Nothing
    findAlt (Alt nm' ascs:alts)
      | nm == nm' = Just ascs
      | otherwise = findAlt alts






termNameInContext
  :: Context -> String -> ElabDecomposer Term
termNameInContext (Context { nominalContext = ds })
                  nm =
  
  findInDeclarations ds
  
  where
    findInDeclarations [] = failure (TermNameNotInScope nm)
    findInDeclarations (TermDeclaration nm' tv:ds')
      | nm == nm' = return tv
      | otherwise = findInDeclarations ds'
    findInDeclarations (_:ds') = findInDeclarations ds'






typeVariableInHypotheticalContext
  :: HypotheticalContext -> String -> ElabDecomposer Kind
typeVariableInHypotheticalContext [] y =
  failure (TypeVariableNotInScope y)
typeVariableInHypotheticalContext (HasKind x k : _) y | x == y =
  return k
typeVariableInHypotheticalContext (_ : hypctx) y =
  typeVariableInHypotheticalContext hypctx y






termVariableInHypotheticalContext
  :: HypotheticalContext -> String -> ElabDecomposer Term
termVariableInHypotheticalContext [] y =
  failure (TermVariableNotInScope y)
termVariableInHypotheticalContext (HasType x u : _) y | x == y =
  return u
termVariableInHypotheticalContext (_ : hypctx) y =
  termVariableInHypotheticalContext hypctx y







noRepeatedConstructors :: [Clause] -> ElabDecomposer ()
noRepeatedConstructors cls =
  do let cs = [ c | Clause c :$: [_] <- cls ]
         uniqueCs = nub cs
         repeats = nub (cs \\ uniqueCs)
     unless (null repeats)
       (failure (RepeatedConstructorsInCase repeats))






coversAllConstructors :: Context
                      -> String
                      -> [Clause]
                      -> ElabDecomposer ()
coversAllConstructors ctx nm cls =
  do let cs = extractCons ctx
         missing = cs \\ [ c | Clause c :$: [_] <- cls ]
     unless (null missing)
       (failure (MissingConstructorsInCase missing))
  where
    extractCons (Context { nominalContext = ds }) =
      extractFromDeclarations ds
    
    extractFromDeclarations [] = []
    extractFromDeclarations (DataDeclaration nm' _ alts:ds)
      | nm == nm' = [ connm | Alt connm _ <- alts ]
      | otherwise = extractFromDeclarations ds
    extractFromDeclarations (_:ds) = extractFromDeclarations ds






signatureOfBuiltin :: String -> ElabDecomposer ([Term], Term)
signatureOfBuiltin n =
  case lookup n builtinSigs of
    Nothing -> failure (UnknownBuiltinName n)
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
           , conTH "Bool" []
           -- , scottBool
           ))
      , ("lessThanEqualsInteger"
        , ( [integerTH, integerTH]
          , conTH "Bool" []
          -- , scottBool
          ))
      , ("greaterThanInteger"
        , ( [integerTH, integerTH]
          , conTH "Bool" []
          -- , scottBool
          ))
      , ("greaterThanEqualsInteger"
        , ( [integerTH, integerTH]
          , conTH "Bool" []
          -- , scottBool
          ))
      , ("equalsInteger"
        ,  ( [integerTH, integerTH]
           , conTH "Bool" []
           -- , scottBool
           ))
      , ("integerToFloat", ([integerTH], floatTH))
      , ("integerToByteString", ([integerTH], byteStringTH))
      
      
      , ("addFloat", ([floatTH, floatTH], floatTH))
      , ("subtractFloat", ([floatTH, floatTH], floatTH))
      , ("multiplyFloat", ([floatTH, floatTH], floatTH))
      , ("divideFloat", ([floatTH, floatTH], floatTH))
      , ("lessThanFloat"
        ,  ( [floatTH, floatTH]
           , conTH "Bool" []
           -- , scottBool
           ))
      , ("lessThanEqualsFloat"
        , ( [floatTH, floatTH]
          , conTH "Bool" []
          -- , scottBool
          ))
      , ("greaterThanFloat"
        , ( [floatTH, floatTH]
          , conTH "Bool" []
          -- , scottBool
          ))
      , ("greaterThanEqualsFloat"
        , ( [floatTH, floatTH]
          , conTH "Bool" []
          -- , scottBool
          ))
      , ("equalsFloat"
        ,  ( [floatTH, floatTH]
           , conTH "Bool" []
           -- , scottBool
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
           , conTH "Bool" []
           -- , scottBool
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





synthCompBuiltin :: String -> ElabDecomposer Term
synthCompBuiltin "txhash" = return byteStringTH
synthCompBuiltin "blocknum" = return integerTH
synthCompBuiltin "blocktime" =
  return (conTH "DateTime" [])
synthCompBuiltin n = failure (UnknownCompBuiltinName n)





enforceLanguageOptionsUsesConstructors :: ElabDecomposer ()
enforceLanguageOptionsUsesConstructors =
  do s <- get
     if NoConstructors `elem` languageOptions s
        then failure LanguageOptionNoConstructors
        else return ()



enforceLanguageOptionsUsesFixedPointTypes :: ElabDecomposer ()
enforceLanguageOptionsUsesFixedPointTypes =
  do s <- get
     if FixedPointTypes `elem` languageOptions s
        then return ()
        else failure LanguageOptionFixedPointTypes




programJ :: Program -> ElabDecomposer ()
programJ (Program decls) =
  forM_ (zip (inits decls) decls) $ \(ds, d) ->
    goal (ElabDeclJ ds d)






declJ :: NominalContext
      -> Declaration
      -> ElabDecomposer ()
declJ ds (DataDeclaration tcn ksigs alts) =
  do enforceLanguageOptionsUsesConstructors
     freshTypeConstructor ds tcn
     let nomctxAddition = DataDeclaration tcn ksigs []
     forM_ alts $ \alt ->
       goal (ElabAltJ
              (nomctxAddition:ds)
              alt
              ksigs)
declJ ds (TypeDeclaration tnm u) =
  do freshTypeName ds tnm
     goal (IsTypeValueJ u)
     _ <- goal (IsTypeJ (Context ds []) u)
     return ()
declJ ds (TermDeclaration nm t) =
  do freshTermName ds nm
     k <- goal (IsTypeJ (Context ds []) t)
     case k of
       TypeK -> return ()
       _ -> failure (TermDeclarationTypeIsNotType nm t k)
declJ ds (TermDefinition nm v) =
  do undefinedTermName ds nm
     u <- termNameInContext
            (Context ds [])
            nm
     goal (IsTermValueJ v)
     let tenv = nominalContextToTypeEnv (Context ds [])
         normal_u = evaluateType tenv u
     goal (CheckJ (Context ds []) normal_u v)





altJ :: NominalContext
     -> Alt
     -> [KindSig]
     -> ElabDecomposer ()
altJ ds (Alt cn ascs) ksigs =
  do freshTermConstructor ds cn
     let hypctx = [ HasKind x k | KindSig x k <- ksigs ]
         xs =  [ Var (Free (FreeVar x)) | KindSig x _ <- ksigs ]
     forM_ ascs $ \asc ->
       do let a = instantiate asc xs
          k' <- goal
                  (IsTypeJ
                    (Context ds hypctx)
                    a)
          unless (k' == TypeK)
            (failure (TermConstructorArgumentKindIsNotType cn a k'))
          return ()
     return ()







isTypeJ :: Context -> Term -> ElabDecomposer Kind
isTypeJ ctx (Var (Free (FreeVar x))) =
  typeVariableInHypotheticalContext (hypotheticalContext ctx) x
isTypeJ _ (Var (Bound _ _)) =
  error "Cannot synth the kind of bound type variables. This should\
        \ never be reachable."
isTypeJ ctx (Decname n :$: []) =
  typeNameInContext ctx n
isTypeJ ctx (FunT :$: [a,b]) =
  do k <- goal (IsTypeJ ctx (instantiate0 a))
     unless (k == TypeK)
       (failure (FunTypeArgumentIsNotType (instantiate0 a) k))
     k' <- goal (IsTypeJ ctx (instantiate0 b))
     unless (k' == TypeK)
       (failure (FunTypeReturnIsNotType (instantiate0 b) k'))
     return TypeK
isTypeJ ctx (ConT c :$: as) =
  do enforceLanguageOptionsUsesConstructors
     ks <- typeConstructorInContext ctx c
     unless (length as == length ks)
       (failure
         (TypeConstructorWrongNumberOfArguments c (length ks) (length as)))
     zipWithM_
       (\a k -> 
         do let a0 = instantiate0 a
            k' <- goal (IsTypeJ ctx a0)
            unless (k == k')
              (failure
                (TypeConstructorWrongArgumentKind c a0 k k'))
            return ())
       as
       ks
     return TypeK
isTypeJ ctx (FixT :$: [sc]) =
  do enforceLanguageOptionsUsesFixedPointTypes
     let (_, [n], a) = openScope (hypotheticalContext ctx) sc
         ctx' = ctx { hypotheticalContext =
                        HasKind n TypeK : hypotheticalContext ctx
                    }
     k' <- goal (IsTypeJ ctx' a)
     unless (k' == TypeK)
       (failure (FixBodyNotType a k'))
     return TypeK
isTypeJ ctx (CompT :$: [a]) =
  do k <- goal (IsTypeJ ctx (instantiate0 a))
     unless (k == TypeK)
       (failure (CompArgumentNotType (instantiate0 a) k))
     return TypeK
isTypeJ ctx (ForallT k :$: [sc]) =
  do let (_, [n], a) = openScope (hypotheticalContext ctx) sc
         ctx' = ctx { hypotheticalContext =
                        HasKind n k : hypotheticalContext ctx
                    }
     k' <- goal (IsTypeJ ctx' a)
     unless (k' == TypeK)
       (failure (ForallBodyNotType a k'))
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
                (TypeApplicationArgumentKindMismatch (instantiate0 b) k' k'''))
            return k''
       _ -> failure (TypeApplicationOfNonFunctionKind (instantiate0 a) k)
isTypeJ _ m =
  failure (CannotSynthKindOfNonType m)






isTypeValueJ :: Term -> ElabDecomposer ()
isTypeValueJ (Var _) =
  return ()
isTypeValueJ (Decname _ :$: []) =
  return ()
isTypeValueJ (FunT :$: [a,b]) =
  do goal (IsTypeValueJ (instantiate0 a))
     goal (IsTypeValueJ (instantiate0 b))
isTypeValueJ (ConT _ :$: as) =
  do enforceLanguageOptionsUsesConstructors
     forM_ as $ \a ->
       goal (IsTypeValueJ (instantiate0 a))
isTypeValueJ (FixT :$: [_]) =
  do enforceLanguageOptionsUsesFixedPointTypes
     return ()
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
  failure (TypeIsNotTypeValue a)






isTermValueJ :: Term -> ElabDecomposer ()
isTermValueJ (Abst :$: [_]) =
  return ()
isTermValueJ (Lam :$: [_]) =
  return ()
isTermValueJ (Con _ :$: ms) =
  do enforceLanguageOptionsUsesConstructors
     forM_ ms $ \m ->
       goal (IsTermValueJ (instantiate0 m))
isTermValueJ (Wrap :$: [_]) =
  do enforceLanguageOptionsUsesFixedPointTypes
     return ()
isTermValueJ (Success :$: [m]) =
  goal (IsTermValueJ (instantiate0 m))
isTermValueJ (Failure :$: []) =
  return ()
isTermValueJ (CompBuiltin _ :$: []) =
  return ()
isTermValueJ (Bind :$: [m,_]) =
  goal (IsTermValueJ (instantiate0 m))
isTermValueJ m =
  failure (TermIsNotTermValue m)






checkJ :: Context -> Term -> Term -> ElabDecomposer ()
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
  do enforceLanguageOptionsUsesConstructors
     (bscs, tc) <- termConstructorInContext ctx c'
     unless (tc == c)
       (failure (TermConstructorCheckedAtWrongType c' tc c))
     unless (length bscs == length ms)
       (failure
         (TermConstructorWrongNumberOfArguments c' (length bscs) (length ms)))
     let as' = map instantiate0 as
         bs = map (\bsc -> instantiate bsc as') bscs
         tenv = nominalContextToTypeEnv ctx
         normal_bs = map (evaluateType tenv) bs
     forM_ (zip normal_bs ms) $ \(b,m) ->
       goal (CheckJ ctx b (instantiate0 m))
checkJ ctx t (Case :$: (m:clsscs)) =
  do enforceLanguageOptionsUsesConstructors
     a <- goal (SynthJ ctx (instantiate0 m))
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
         failure (CaseScrutineeNotConstructedData (instantiate0 m) a)
checkJ ctx a@(FixT :$: [sc]) (Wrap :$: [m]) =
  do enforceLanguageOptionsUsesFixedPointTypes
     let b = instantiate sc [a]
         tenv = nominalContextToTypeEnv ctx
         normal_b = evaluateType tenv b
     goal (CheckJ ctx normal_b (instantiate0 m))
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
      error "Cannot check the type of a type. This should never happen."
    (False,_) ->
      error "Cannot check against a term. This should never happen."






synthJ :: Context -> Term -> ElabDecomposer Term
synthJ ctx (Var (Free (FreeVar x))) =
  do t <- termVariableInHypotheticalContext (hypotheticalContext ctx) x
     let tenv = nominalContextToTypeEnv ctx
         normal_t = evaluateType tenv t
     return normal_t
synthJ _ (Var (Bound _ _)) =
  error "Cannot synth the type of a bound term variable. This\
        \ should never be reachable."
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
              (failure (InstantiationAtWrongKind (instantiate0 m) (instantiate0 a) k k'))
            let tenv = nominalContextToTypeEnv ctx
            return (evaluateType tenv (instantiate sc [instantiate0 a]))
       _ -> failure (InstantiationOfNonForallType (instantiate0 m) b)
synthJ ctx (App :$: [m,n]) =
  do a <- goal (SynthJ ctx (instantiate0 m))
     case a of
       FunT :$: [b,c] ->
         do let tenv = nominalContextToTypeEnv ctx
                normal_b = evaluateType tenv (instantiate0 b)
            goal (CheckJ ctx normal_b (instantiate0 n))
            return (instantiate0 c)
       _ -> failure (ApplicationOfNonFunctionType (instantiate0 m) a)
synthJ ctx (Unwrap :$: [m]) =
  do enforceLanguageOptionsUsesFixedPointTypes
     a <- goal (SynthJ ctx (instantiate0 m))
     case a of
       FixT :$: [sc] ->
         let b = instantiate sc [a]
             tenv = nominalContextToTypeEnv ctx
             normal_b = evaluateType tenv b
         in return normal_b
       _ -> failure (CannotUnwrapNonFixedPointType (instantiate0 m) a)
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
              CompT :$: [_] -> return c
              _ -> failure (BindBodyNotCompType m0 c)
       _ -> failure
              (BindArgumentNotCompType (instantiate0 m) a)
synthJ _ (PrimInteger _ :$: []) =
  return integerTH
synthJ _ (PrimFloat _ :$: []) =
  return floatTH
synthJ _ (PrimByteString _ :$: []) =
  return byteStringTH
synthJ ctx (Builtin n :$: ms) =
  do (as,b) <- signatureOfBuiltin n
     unless (length as == length ms)
       (failure (BuiltinWrongNumberOfArguments n (length as) (length ms)))
     let tenv = nominalContextToTypeEnv ctx
         normal_as = map (evaluateType tenv) as
     forM_ (zip normal_as ms) $ \(a,m) ->
       goal (CheckJ ctx a (instantiate0 m))
     return b
synthJ _ m =
  failure (CannotSynthType m)






clauseJ
  :: Context
  -> String
  -> [Term]
  -> Term
  -> Clause
  -> ElabDecomposer ()
clauseJ ctx tc as t (Clause c :$: [sc]) =
  do (bscs, tc') <- termConstructorInContext ctx c
     unless (tc == tc')
       (failure (ClauseConstructorWrongType c tc tc'))
     unless (length bscs == length (names sc))
       (failure
         (ClauseConstructorWrongNumberOfArguments c (length bscs) (length (names sc))))
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





equalJ :: Context -> Term -> Term -> ElabDecomposer ()
equalJ _ (Var x) (Var y) =
  if x == y
    then return ()
    else failure (VariablesNotEqual x y)
equalJ ctx@(Context nomctx _) m0@(c :$: scs) m0'@(c' :$: scs') =
  if c /= c'
  then failure (TermsNotEqual m0 m0')
  else forM_ (zip scs scs') $ \(sc,sc') ->
         do let (xs, ns, m) = openScope (hypotheticalContext ctx) sc
                m' = instantiate sc' (map (Var . Free) xs)
                tenv = nominalContextToTypeEnv (Context nomctx [])
                normal_m = evaluateType tenv m
                normal_m' = evaluateType tenv m'
                ctx' = ctx { hypotheticalContext =
                               [ HasType n undefined | n <- ns ]
                                 ++ hypotheticalContext ctx
                           }
            goal (EqualJ ctx' normal_m normal_m')
equalJ _ m m' =
  failure (TermsNotEqual m m')




equalAllJ :: Context -> Term -> [Term] -> ElabDecomposer ()
equalAllJ _ _ [] = return ()
equalAllJ ctx a (b:bs) =
  do goal (EqualJ ctx a b)
     goal (EqualAllJ ctx a bs)