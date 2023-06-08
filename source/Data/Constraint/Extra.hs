{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Extra tools for dealing with constraints.
module Data.Constraint.Extra
  ( type (&&),
    Trivial,
  )
where

import Data.Kind (Constraint, Type)

-- | A trivial constraint satisfied by all types.
type Trivial :: Type -> Constraint
class Trivial x

instance Trivial x

-- | Products of constraints.
type (&&) :: (Type -> Constraint) -> (Type -> Constraint) -> Type -> Constraint
class (c x, d x) => (c && d) x

instance (c x, d x) => (c && d) x
