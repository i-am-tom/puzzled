module NewConstrDefVarMonad where

class NewConstrDefVarMonad c m v | m -> c , m -> v where
    new :: (c a) => m (v a)
    read :: (c a) => v a -> m a
    write :: (c a) => v a -> a -> m ()

new' :: (Monad m, NewConstrDefVarMonad c m v, c a) => a -> m (v a)
new' x = do
    v <- new
    write v x
    return v 