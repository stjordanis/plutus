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








-- * Decomposition

-- | A `Decomposer` is a special kind of reified program which is used for
-- decomposing concrete representations of program problems into
-- sequences of subproblems which can depend on the results of earlier
-- subproblems. A good example of this in the context of programming language
-- implementation is an evaluator, which decomposes the problem of evaluating
-- a whole expression into evaluating its parts, and then doing something
-- with the results.
--
-- A `Program` acts somewhat like a call stack data type, so a `Decomposer`
-- is a thing which explains how to take the current problem being worked
-- on by a machine and expand it into those things which must be added to the
-- call stack.
--
-- Decomposers might require state, of course, because the decomposition
-- process in domains like proof theory or type theory sometimes require that
-- we do things like name generation. They also can fail.

type Decomposer s e g = ProgramT g (StateT s (Either e))


-- | To build decomposers, we must have something to decompose. In particular,
-- we have an indexed type `g` (for "goal", in a proof search sense), which
-- has index `a` describing the type of its synthesized/returned data. Given
-- any goal, we must be able to form a decomposer from it, which is the
-- program representing the subproblems required to achieve that goal.

class Decomposable s e g where
  decompose :: g a -> Decomposer s e g a


-- | `failure` is a trivial decomposer that takes an error message and just
-- immediately kills the decomposition program.

failure :: e -> Decomposer s e g a
failure = lift . throwError


-- | `goal` is a simple decomposer which wraps up a goal element without
-- decomposing it, so that a proof system can inspect the goals during error
-- reporting.

goal :: g a -> Decomposer s e g a
goal = singleton





-- * Metavariables

-- | Many systems, such as Prolog, have metavariables as part of their design,
-- where the process of decomposing goals into subgoals requires having fully
-- instantiated all the metavariables that are getting inspected by the
-- decomposer. As such, we build this into the system from the outset, so that
-- you don't need to explicitly do metavariable substitution in your code.
--
-- The `Metas` type class encodes the capability of a decomposition state `s`
-- and a goal type `g` to be used for substitution. `s` should have all the
-- solutions for metavariables, while `g i` should have the uses of metavars,
-- and so we ought to be able to use the proof state like an environment and
-- substitute its metas in any given goal.

class Metas s g where
  substitute :: s -> g i -> g i


-- | The `Any` type existentially closes over the return type of a goal, so
-- we can put goals into collections for error reporting.

data Any f where
  Any :: f i -> Any f

substituteAny :: Metas s g => s -> Any g -> Any g
substituteAny s (Any g) = Any (substitute s g)


-- | A `ProofContext` is just a stack of goals marked with their position as a
-- subgoal of their parent goal one up the stack.

type ProofContext g = [(Int,Any g)]

substituteContext :: Metas s g => s -> ProofContext g -> ProofContext g
substituteContext subs = map (\(i,x) -> (i, substituteAny subs x))


-- | `ProofError`s wrap up all of the information that might be needed to
-- properly report on why a failure occurs, including an error message, the
-- proof state, the problem context, and the current goal that caused the
-- failure.

data ProofError s e g =
  ProofError { proofError :: e
             , proofState :: s
             , proofContext :: ProofContext g
             , proofGoal :: Any g
             }

class ShowProofError s e g where
  showProofError :: ProofError s e g -> String


-- | A `ProofDeveloper` is a stateful program which might fail, which tracks
-- the proof context explicitly for error reporting purposes.

type ProofDeveloper s e g = ReaderT (ProofContext g)
                              (StateT s
                                (Either (ProofError s e g)))

runProofDeveloper :: ProofDeveloper s e g a
                  -> ProofContext g
                  -> s
                  -> Either (ProofError s e g) (a,s)
runProofDeveloper l ctx s =
  runStateT (runReaderT l ctx) s


-- | To actually throw an error, we simply grab all the relevant information
-- and throw into the underlying `Either`.

throwProofError :: Metas s g => Any g -> e -> ProofDeveloper s e g a
throwProofError g e =
  do ctx <- ask
     s <- get
     throwError
       (ProofError e
                   s
                   (substituteContext s ctx)
                   (substituteAny s g))





-- * Unrolling goals into computations


-- | Given a goal, we can build a proof developer for the entire process of
-- solving it by decomposing into its immediate sub-problems and then
-- recursively solving those by unrolling the decomposer `Program` into
-- computations as well.

proofDeveloper :: (Metas s g, Decomposable s e g) => g r -> ProofDeveloper s e g r
proofDeveloper g =
  do s <- get
     unroll 0 (Any g) (decompose (substitute s g))


-- | Unrolling a decomposer just involves sequentially peaking at the goals
-- represented by the `Program`, and then monadically chaining together their
-- proof developers. But because we wish to track the context of each goal
-- for error reporting purposes, we extend each subgoal's unrolling to track
-- what goal lead to that unrolling.

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