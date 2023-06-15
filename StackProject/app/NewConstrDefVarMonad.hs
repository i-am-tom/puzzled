module NewConstrDefVarMonad where

class NewConstrDefVarMonad c m v | m -> c where
    new :: (c a) => m (v a)
    read :: (c a) => v a -> m a
    write :: (c a) => v a -> a -> m ()