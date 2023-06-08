{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Extra tools for dealing with constraints.
module Data.Constraint.Extra
  ( type (&&),
    Trivial,

    type (-->) (..),
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

type (-->) :: (Type -> Constraint) -> (Type -> Constraint) -> Constraint
class (forall x. c x => d (Solo x)) => c --> d where
  given :: c x => (d (Solo x) => r) -> r

instance (forall x. c x => d (Solo x)) => c --> d where
  given x = x
