module NewConstrDefVarMonad where

import Data.Kind

class NewConstrDefVarMonad c m v | m -> c where
    new :: (c a) => m (v a)
    read :: (c a) => v a -> m a
    write :: (c a) => v a -> a -> m ()

data FNCDVarMonad c v r where
    FNCDNew :: (c a) => FNCDVarMonad c v (v a)
    FNCDRead :: (c a) => v a -> FNCDVarMonad c v a
    FNCDWrite :: (c a) => v a -> a -> FNCDVarMonad c v ()

instance NewConstrDefVarMonad c (FNCDVarMonad c v) v where
    new = FNCDNew
    read = FNCDRead
    write = FNCDWrite