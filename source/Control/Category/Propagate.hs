{-# LANGUAGE ExplicitNamespaces #-}

-- |
-- Categories that allow equalities between variables.
module Control.Category.Propagate where

import ConCat.Category (ClosedCat, Ok, type (&&))
import Data.Kind (Constraint, Type)

-- | A 'Propagate' category allows us to assert that two sides of a tensor are
-- equal, and have that equality propagate throughout the arrows within the
-- category.
type Propagate :: (Type -> Type -> Type) -> Constraint
class (ClosedCat k) => Propagate k where
  -- | Fork the computation. In one fork, select the left-hand value. In the
  -- other, select the right-hand value.
  choice :: (Ok k x) => k (x && x) x

  -- | Map a tensor of two values to their merged value, now asserting that the
  -- two are entirely equal.
  unify :: (Ok k x) => k (x && x) x
