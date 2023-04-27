{-# LANGUAGE NoImplicitPrelude, RebindableSyntax #-}
module ConstrainedMonad where

import Prelude hiding (return, (>>=), (>>))
import Data.Kind

class CMonad c m | m -> c where
    return :: (c a) => a -> m a
    (>>=) :: (c a) => m a -> (a -> m b) -> m b

class Determine (m :: Type -> Type) (c :: Type -> Constraint) | m -> c

instance (Monad m, Determine m c) => CMonad c m where
    return = return
    (>>=) = (>>=)

test :: (CMonad c m, c Int) => m Int
test = do 
    x <- return 3
    return (x + 4)