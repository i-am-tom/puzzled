{-# LANGUAGE NoImplicitPrelude #-}
module Experiments.LambdaCalc where

import Prelude hiding (read)
import NewConstrDefVarMonad
import LambdaVarMonad
import Lambda (LambdaF)
import DTC
import DTCFunctions.BakeContext
import Lattice
import Data.Maybe
import Data.IORef

reduction :: forall c m v . (
      Monad m
    , c (Fix (TB LambdaF :.: v))
    , NewConstrDefVarMonad c m v) =>
    m (Fix (TB LambdaF))
reduction = do
    expr <- (lam' (var' @(TB LambdaF) 0)) <^>* (var' 1)
    bakeContext @(TB LambdaF) =<< read expr

{-}
instance (Top :<: f) => Top :<: (TB f :.: v) where
    inj Top = CIRC TTOP
    proj (CIRC TTOP) = Just Top
    proj _ = Nothing
    -}

instance Lattice (TB IORef a) where
    x /\ y 
        | x == y = x
        | otherwise = TBOT
    x \/ y
        | x == y = x
        | otherwise = TTOP

test :: IO (Fix (TB LambdaF))
test = reduction @_ @_ @(IORef)