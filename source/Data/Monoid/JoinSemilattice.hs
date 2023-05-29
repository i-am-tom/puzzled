{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

-- |
-- Idempotent, commutative monoids.
module Data.Monoid.JoinSemilattice
  ( Merge (Changed, Unchanged),
    JoinSemilattice (..),
  )
where

import Data.Kind (Constraint, Type)
import Data.Semigroup (All, Any (Any, getAny), Max, Min)
import Data.Set (Set)

-- | A 'JoinSemilattice' is a 'Monoid' that obeys the following laws:
--
--     x <> y === y <> x
--     x <> x === x
--
-- These properties mean that we never need to queue a given propagator more
-- than once, /and/ we don't need to worry about the order of execution.
type JoinSemilattice :: Type -> Constraint
class (Monoid x) => JoinSemilattice x where
  -- | A 'mappend' operation that frames the operation as merging the right
  -- value into the left one, reporting the result of the 'Merge'.
  (<~) :: x -> x -> Merge x
  default (<~) :: (Eq x) => x -> x -> Merge x
  x <~ y = let z = x <> y in Merge (x /= z, z)

  -- | Does the left value imply the right? Specifically, would the left
  -- value be 'changed' if we merged the right value into it?
  implies :: x -> x -> Bool
  implies x y = case x <~ y of
    Unchanged _ -> True
    Changed _ -> False

instance JoinSemilattice ()

instance JoinSemilattice Any

instance JoinSemilattice All

instance (Bounded x, Ord x) => JoinSemilattice (Max x)

instance (Bounded x, Ord x) => JoinSemilattice (Min x)

instance (Ord x) => JoinSemilattice (Set x) where
  x <~ y
    | length x < length y = Changed z -- Keep z lazy if possible
    | length z > length x = Changed z
    | otherwise = Unchanged z
    where
      z = x <> y

instance (JoinSemilattice x) => JoinSemilattice (Merge x) where
  Merge (cx, rx) <~ Merge (cy, ry) = do
    cz <- fmap getAny (Any cx <~ Any cy)
    rz <- rx <~ ry

    pure (Merge (cz, rz))

-- | The result of merging one value into another.
type Merge :: Type -> Type
newtype Merge x = Merge (Bool, x)
  deriving stock (Eq, Functor, Ord)
  deriving (Applicative, Monad) via (,) Any
  deriving (Semigroup, Monoid) via (Any, x)

{-# COMPLETE Changed, Unchanged #-}

instance (Show x) => Show (Merge x) where
  showsPrec p = \case
    Changed x ->
      showParen (p >= 11) $
        showString "Changed "
          . showsPrec 11 x
    Unchanged x ->
      showParen (p >= 11) $
        showString "Unchanged "
          . showsPrec 11 x

pattern Changed :: x -> Merge x
pattern Changed x = Merge (True, x)

pattern Unchanged :: x -> Merge x
pattern Unchanged x = Merge (False, x)
