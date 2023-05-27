{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- |
-- A class hierarchy for various types of category.
module Control.Category.Hierarchy where

import Data.Kind (Constraint, Type)
import Prelude qualified

-- | We define categories in terms of their morphisms, and say that a category
-- must have a defined identity morphism (mapping every element to itself) and
-- associative composition of morphisms.
type Category :: (Type -> Type -> Type) -> Constraint
class Category k where
  -- | The class of objects allowed within this category. By default, objects
  -- in the category are totally unconstrained.
  type Object k :: Type -> Constraint

  type Object k = Trivial

  -- | The identity morphism.
  id :: (Object k x) => k x x

  -- | Composition of morphisms.
  (.) :: (Object k x, Object k y, Object k z) => k y z -> k x y -> k x z

instance Category (->) where
  id = Prelude.id
  (.) = (Prelude..)

-- | A trivial constraint satisfied by all types.
type Trivial :: Type -> Constraint
class Trivial x

instance Trivial x

-- | Products of constraints.
type (&&) :: (Type -> Constraint) -> (Type -> Constraint) -> Type -> Constraint
class (c x, d x) => (c && d) x

instance (c x, d x) => (c && d) x
