{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Extra tools for dealing with constraints.
module Data.Constraint.Extra
  ( type (&&),
    Trivial,
    type (~>) (..),
  )
where

import Data.Kind (Constraint, Type)
import Data.Tuple (Solo)

-- | A trivial constraint satisfied by all types.
type Trivial :: Type -> Constraint
class Trivial x

instance Trivial x

-- | Products of constraints.
type (&&) :: (Type -> Constraint) -> (Type -> Constraint) -> Type -> Constraint
class (c x, d x) => (c && d) x

instance (c x, d x) => (c && d) x

-- | A constraint that witnesses a constraint implication. It would be really
-- nice not to have 'Solo' here - in fact, it would be nice not to have this
-- class at all - but no dice:
--
-- https://gitlab.haskell.org/ghc/ghc/-/issues/15636
type (~>) :: (Type -> Constraint) -> (Type -> Constraint) -> Constraint
class (forall x. (c x) => d (Solo x)) => c ~> d where
  -- | If we can produce @r@ given @d@, then we should be able to produce it
  -- given @c@ too.
  given :: (c x) => ((d (Solo x)) => r) -> r

instance (forall x. (c x) => d (Solo x)) => c ~> d where
  given x = x
