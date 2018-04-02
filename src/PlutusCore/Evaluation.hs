{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}





-- | This module defines how to evaluate terms in the simply typed lambda
-- calculus w/ non-parametric user defined types (eg Bool, Nat).

module PlutusCore.Evaluation where

--import Utils.ABTs.ABT
--import Utils.Env
--import Utils.Eval
--import Utils.Names
--import Utils.ABTs.Pretty (pretty)
import qualified PlutusCore.CKMachine as CK
--import PlutusCore.BuiltinEvaluation
import PlutusCore.EvaluatorTypes
--import PlutusCore.PatternMatching
import PlutusCore.Term
--import PlutusShared.Qualified

import Data.Either (isRight)
import qualified Cardano.Crypto.Wallet as CC
--import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.ByteString.Lazy as BS










tick :: (Num s, MonadState s m) => m ()
tick = modify (subtract 1)

type PetrolEvaluator =
  ReaderT (TransactionInfo,Environment) (StateT Petrol (Either String))

declEnvironment :: PetrolEvaluator Environment
declEnvironment = snd <$> ask

signedTransaction :: PetrolEvaluator TransactionInfo
signedTransaction = fst <$> ask



evaluate
  :: CK.BlockChainInfo -> Environment -> Petrol -> Term -> Either String Term
evaluate bci env ptrl m =
  CK.evaluate bci env ptrl m
  {-
  let evlt = meval m :: PetrolEvaluator Term
      result = runStateT (runReaderT evlt (txinfo,env)) ptrl
  in fst <$> result
  -}

evaluateType :: Environment -> Term -> Term
evaluateType env m =
  case evaluate undefined env (Petrol maxBound) m of
    Right u -> u
    Left e -> error (show e) `seq` undefined
  

----------------------------------------------------------------------------
-- Crypto
----------------------------------------------------------------------------

publicKeyLength, signatureLength, chainCodeLength :: Int
publicKeyLength = 32
signatureLength = 64
chainCodeLength = 32

verify :: BS.ByteString -> BS.ByteString -> BS.ByteString -> Bool
verify key val sig = isRight $ do
  key' <- CC.xpub (BS.toStrict key)
  sig' <- CC.xsignature (BS.toStrict sig)
  case CC.verify key' (BS.toStrict val) sig' of
    True  -> Right ()
    False -> Left ""