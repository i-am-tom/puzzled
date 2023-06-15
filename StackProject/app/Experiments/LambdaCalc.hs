module Experiments.LambdaCalc where

import NewConstrDefVarMonad
import LambdaVarMonad
import Lambda (LambdaF)
import DTC

reduction :: forall c m v . (
      Monad m
    , c (Fix (LambdaF :.: v))
    , NewConstrDefVarMonad c m v) =>
    m Bool
reduction = do
    (lam' (var' @LambdaF 0)) <^>* (var' 1)
    return True