{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- |
-- Equality for arrows within a category.
module Control.Category.Eq where

import Data.Kind (Constraint, Type)

-- | Standard 'Eq' requires that the types be identical. However, for our
-- purposes, we only care that the arrow is of the same type - the equality of
-- domain and codomain can be established within the implementation.
type HEq :: (Type -> Type -> Type) -> Constraint
class (forall x y. Eq (k x y)) => HEq k where
  -- | Check whether two arrows are equal.
  --
  -- prop> (x === y) == (x == y)
  (===) :: k a b -> k c d -> Bool

infix 4 ===
