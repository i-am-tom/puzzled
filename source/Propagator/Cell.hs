{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeFamilies #-}

module Propagator.Cell where

import Control.Monad (MonadPlus, join)
import Control.Monad.Primitive (PrimMonad (PrimState), RealWorld)
import Data.Kind (Type)
import Data.Monoid.JoinSemilattice (JoinSemilattice ((<~)), Merge (Changed, Unchanged))
import Data.Primitive.MutVar.Rollback (Ref, atomicModifyMutVar, newMutVar, readMutVar)

-- | Mutable values within our network that can "grow" over time (with respect
-- to some 'JoinSemilattice'). Over time, we may 'Merge' other values into
-- here, moving the result up the lattice.
type Value :: (Type -> Type) -> Type -> Type
type Value m x = Ref (x, m ())

-- | Create a new value in a 'Value' wrapper.
create :: (PrimMonad m, PrimState m ~ RealWorld) => x -> m (Value m x)
create x = newMutVar (x, pure ())

-- | Read the value within a 'Value' wrapper. This does not record provenance,
-- so this should not be used in any user code!
unsafeRead :: (PrimMonad m, PrimState m ~ RealWorld) => Value m x -> m x
unsafeRead = fmap fst . readMutVar

-- | Attach a propagator to a 'Value' to fire whenever the value updates.
watch :: (MonadPlus m, PrimMonad m, PrimState m ~ RealWorld, JoinSemilattice x) => Value m x -> (x -> m ()) -> m ()
watch ref p = join $ atomicModifyMutVar ref \(x, ps) -> ((x, p' *> ps), p')
  where
    p' = readMutVar ref >>= p . fst

-- | Write information to a 'Value', firing its propagators if the value
-- changes.
write :: (MonadPlus m, PrimMonad m, PrimState m ~ RealWorld, JoinSemilattice x) => Value m x -> x -> m ()
write ref x = join do
  atomicModifyMutVar ref \(y, ps) ->
    case x <~ y of
      Changed z -> ((z, ps), ps)
      Unchanged _ -> ((x, ps), pure ())
