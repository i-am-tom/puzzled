{-# LANGUAGE NoImplicitPrelude #-}
module Experiments.LambdaCalc where

import Prelude hiding (read)
import NewConstrDefVarMonad
import LambdaVarMonad
import Lambda
import DTC
import Lattice
import Data.Maybe
import Data.IORef
import DTCFunctions.SwitchContext

reduction :: forall c m v . (
      Monad m
    , c (Fix (TB LambdaF :.: TB v))
    , NewConstrDefVarMonad c m (TB v)) =>
    m (Fix (TB LambdaF))
reduction = do
    expr <- (lam' (var' @(TB LambdaF) 0)) <^>* (var' 1)
    evl <- read expr >>= fmap res . foldFNCD (switchAlg evalStepAlg) 
    bakeContext @(TB LambdaF) evl -- =<< read expr


instance Top :<: (TB f :.: v) where
    inj Top = CIRC TTOP
    proj (CIRC TTOP) = Just Top
    proj _ = Nothing

instance Lattice (TB IORef a) where
    x /\ y 
        | x == y = x
        | otherwise = TBOT
    x \/ y
        | x == y = x
        | otherwise = TTOP

concreteReductionTest :: IO (Fix (TB LambdaF))
concreteReductionTest = reduction