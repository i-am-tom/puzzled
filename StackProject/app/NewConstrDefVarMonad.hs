{-# LANGUAGE NoImplicitPrelude #-}
module NewConstrDefVarMonad where

import Prelude hiding (read)
import Data.IORef
import DTC
import Control.Monad
import BaseVarMonadRenamed
import Data.Kind
import BaseVarMonad ()
import Lattice
import BaseVarMonadRenamed (bvmRead)

class NewConstrDefVarMonad c m v | m -> c , m -> v where
    new :: (c a) => m (v a)
    read :: (c a) => v a -> m a
    write :: (c a) => v a -> a -> m ()

new' :: (Monad m, NewConstrDefVarMonad c m v, c a) => a -> m (v a)
new' x = do
    v <- new
    write v x
    return v 
    

class IDC a where
instance IDC a


instance NewConstrDefVarMonad BoundedJoinSemilattice IO IORef where
    new = bvmNew top
    read = bvmRead
    write = bvmWrite

class ConstrainedReadVarMon c m v | m -> c where
    cread :: (c a) => v a -> m a

instance (NewConstrDefVarMonad c m v) => ConstrainedReadVarMon c m v where 
    cread = read

class (ConstrainedReadVarMon IDC m v) => ReadVarMon m v
instance (ConstrainedReadVarMon IDC m v) => ReadVarMon m v

foldFNCD :: (
      c (Fix (f :.: v))
    , Functor f
    , Monad m
    , ConstrainedReadVarMon c m v) => 
    Algebra f (m a) -> Fix (f :.: v) -> m a
foldFNCD = foldCM cread