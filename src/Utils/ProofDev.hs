{-# OPTIONS -Wall #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Utils.ProofDev where

import Control.Monad.Except
import Control.Monad.Operational
import Control.Monad.Reader
import Control.Monad.State









type Decomposer s e g = ProgramT g (StateT s (Either e))

class Decomposable s e g where
  decompose :: g a -> Decomposer s e g a

failure :: e -> Decomposer s e g a
failure = lift . throwError

goal :: g a -> Decomposer s e g a
goal = singleton






class Metas s g where
  substitute :: s -> g i -> g i


data Any f where
  Any :: f i -> Any f

substituteAny :: Metas s g => s -> Any g -> Any g
substituteAny s (Any g) = Any (substitute s g)

type ProofContext a = [(Int,a)]

substituteContext :: Metas s g => s -> ProofContext (Any g) -> ProofContext (Any g)
substituteContext subs = map (\(i,x) -> (i, substituteAny subs x))

data ProofError s e g =
  ProofError { proofError :: e
             , proofState :: s
             , proofContext :: ProofContext (Any g)
             , proofGoal :: Any g
             }

class ShowProofError s e g where
  showProofError :: ProofError s e g -> String



type ProofDeveloper s e g = ReaderT (ProofContext (Any g))
                              (StateT s
                                (Either (ProofError s e g)))

runProofDeveloper :: ProofDeveloper s e g a
                  -> ProofContext (Any g)
                  -> s
                  -> Either (ProofError s e g) (a,s)
runProofDeveloper l ctx s =
  runStateT (runReaderT l ctx) s

throwProofError :: Metas s g => Any g -> e -> ProofDeveloper s e g a
throwProofError g e =
  do ctx <- ask
     s <- get
     throwError
       (ProofError e
                   s
                   (substituteContext s ctx)
                   (substituteAny s g))






proofDeveloper :: (Metas s g, Decomposable s e g) => g r -> ProofDeveloper s e g r
proofDeveloper g =
  do s <- get
     unroll 0 (Any g) (decompose (substitute s g))


unroll :: (Metas s g, Decomposable s e g)
        => Int -> Any g -> Decomposer s e g r -> ProofDeveloper s e g r
unroll i upg d =
  do s <- get
     case runStateT (viewT d) s of
       Left e ->
         throwProofError upg e
       Right (pv,s') ->
         do put s'
            case pv of
              Return x ->
                return x
              g :>>= k ->
                do x <- local ((i,upg):) (proofDeveloper g)
                   unroll (i+1) upg (k x)