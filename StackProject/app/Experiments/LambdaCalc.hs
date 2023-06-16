{-# LANGUAGE NoImplicitPrelude #-}
module Experiments.LambdaCalc where

import Prelude hiding (read)
import NewConstrDefVarMonad
import LambdaVarMonad
import Lambda (LambdaF)
import DTC
import DTCFunctions.BakeContext

reduction :: forall c m v . (
      Monad m
    , c (Fix (LambdaF :.: v))
    , NewConstrDefVarMonad c m v) =>
    m (Fix LambdaF)
reduction = do
    expr <- (lam' (var' @LambdaF 0)) <^>* (var' 1)
    bakeContext =<< read expr

--test :: IO (Fix LambdaF)
--test = reduction