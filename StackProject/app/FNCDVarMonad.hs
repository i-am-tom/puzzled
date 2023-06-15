module FNCDVarMonad where

import NewConstrDefVarMonad

data FNCDVarMonad c v r where
    FNCDNew :: (c a) => FNCDVarMonad c v (v a)
    FNCDRead :: (c a) => v a -> FNCDVarMonad c v a
    FNCDWrite :: (c a) => v a -> a -> FNCDVarMonad c v ()
    FNCDReturn :: a -> FNCDVarMonad c v a
    FNCDBind :: FNCDVarMonad c v a -> (a -> FNCDVarMonad c v b) -> FNCDVarMonad c v b

fncdVoid :: FNCDVarMonad c v a -> FNCDVarMonad c v ()
fncdVoid m = FNCDBind m (const $ FNCDReturn ())

instance NewConstrDefVarMonad c (FNCDVarMonad c v) v where
    new = FNCDNew
    read = FNCDRead
    write = FNCDWrite