module BaseVarMonad where

import Data.IORef

class BaseVarMonad m v where
    new :: a -> m (v a)
    read :: v a -> m a
    write :: v a -> a -> m ()

instance BaseVarMonad IO IORef where
    new = newIORef
    read = readIORef
    write = writeIORef