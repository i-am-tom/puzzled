{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Mutable variable operations with rollback.
--
-- The reason we want to do this is to build a system for modifying variables
-- that allows for rollback. If we imagine some 'BranchT' computation monad
-- where every successful branch represents a result, then we can implement
-- writes in the following shape:
--
--     write ref new = readMutVar ref >>= \old ->
--       writeMutVar ref x <|> writeMutVar ref old *> empty
--
-- Once this branch has been successfully completed _or_ failed, the next
-- branch will undo the write and then fail. the result is that writes are
-- undone from newest to oldest, and we "roll back" the writes in the way we'd
-- expect.
module Data.Primitive.MutVar.Rollback
  ( Primitive.MutVar,
    Ref,
    atomicModifyMutVar,
    writeMutVar,
    Primitive.newMutVar,
    Primitive.readMutVar,
  )
where

import Control.Applicative (empty, (<|>))
import Control.Monad (MonadPlus, join)
import Control.Monad.Primitive (PrimMonad (PrimState), RealWorld)
import Data.Kind (Type)
import Data.Primitive.MutVar qualified as Primitive

-- | A shorthand for mutable variables.
type Ref :: Type -> Type
type Ref = Primitive.MutVar RealWorld

-- | Atomically and strictly modify a mutable variable in the first "branch",
-- and undo the modification in the second "branch".
atomicModifyMutVar :: (MonadPlus m, PrimMonad m, PrimState m ~ RealWorld) => Ref x -> (x -> (x, r)) -> m r
atomicModifyMutVar ref k = join do
  Primitive.atomicModifyMutVar' ref \x -> do
    let rollback = Primitive.atomicModifyMutVar' ref \_ -> (x, ())
    flip fmap (k x) \r -> pure r <|> rollback *> empty

-- | Atomically and strictly write a value to a 'MutVar' with the same rollback
-- mechanism as described for 'atomicModifyMutVar'.
writeMutVar :: (MonadPlus m, PrimMonad m, PrimState m ~ RealWorld) => Ref x -> x -> m ()
writeMutVar ref x = atomicModifyMutVar ref \_ -> (x, ())
