module BaseVarMonad where

class BaseVarMonad m v where
    new :: a -> m (v a)
    read :: v a -> m a
    write :: v a -> a -> m ()