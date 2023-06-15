{-# LANGUAGE NoImplicitPrelude #-}
module RunFNCDVarMonad where

import Prelude hiding (read)
import BaseVarMonad
import FNCDVarMonad
import DTC
import Lattice
import Control.Monad

data PtrCont m a = PtrCont{
    content :: a,
    propagators :: [a -> m ()]
}

runFNCDVarMonad :: (
      BaseVarMonad m v
    , Monad m
    , forall a. (c a) => Eq a
    , forall a. (c a) => BoundedJoinSemilattice a) =>
    FNCDVarMonad c (v :.: (PtrCont m)) a -> m a
runFNCDVarMonad = runFNCDVarMonad' (const $ FNCDReturn ())

runFNCDVarMonad' :: (
      BaseVarMonad m v
    , Monad m
    , forall a. (c a) => Eq a
    , forall a. (c a) => BoundedJoinSemilattice a) =>
    (a -> FNCDVarMonad c (v :.: (PtrCont m)) ()) ->
    FNCDVarMonad c (v :.: (PtrCont m)) a -> m a
runFNCDVarMonad' _  FNCDNew = CIRC <$> new (PtrCont top [])
runFNCDVarMonad' cont (FNCDRead (CIRC v)) = do
    old <- read v
    --TODO: check whether this terminates and does not swallow continuations
    write v (old{propagators = (runFNCDVarMonad' (const $ FNCDReturn ()) . cont) : propagators old})
    return $ content old
runFNCDVarMonad' _ (FNCDWrite (CIRC v) x) = do --WARNING: Not threadsafe!
    old <- read v
    let x' = x /\ content old
    unless (x == x') $ do
        sequence $ map ($ x') (propagators old)
        write v (old{content = x'})
runFNCDVarMonad' _ (FNCDReturn a) = return a
runFNCDVarMonad' cont (FNCDBind ma amb) = (runFNCDVarMonad' (fncdVoid . amb) ma) >>= runFNCDVarMonad' cont . amb