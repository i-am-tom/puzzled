{-# LANGUAGE NoImplicitPrelude #-}
module BaseVarMonadRenamed 
    ( bvmNew
    , bvmRead
    , bvmWrite
    , BaseVarMonad)
    where

import BaseVarMonad

bvmNew :: BaseVarMonad m v => a -> m (v a)
bvmNew = new
bvmRead :: BaseVarMonad m v => v a -> m a
bvmRead = read
bvmWrite :: BaseVarMonad m v => v a -> a -> m ()
bvmWrite = write