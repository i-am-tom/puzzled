{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- |
-- A class hierarchy for various types of category.
module Control.Category.Hierarchy
  ( Category (..),

    Cartesian (..),
    Tensor,
    swap,

    Closed (..),
    Hom,

    -- * Utilities
    Trivial,
    type (&&)
  ) where

import Data.Kind (Constraint, Type)
import Prelude hiding (curry, id, uncurry)

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
  id :: forall x. Object k x => k x x

  -- | Composition of morphisms.
  (.) :: forall x y z. (Object k x, Object k y, Object k z) => k y z -> k x y -> k x z

-------------------------------------------------------------------------------

-- | A type-level representation of tensors within a category. We deliberately
-- don't reuse something like (,) so we can differentiate between tensors and,
-- for example, objects-that-happen-to-be-tuples.
type Tensor :: Type -> Type -> Type
data Tensor x y

-- | Categories with a notion of products (tensors).
type Cartesian :: (Type -> Type -> Type) -> Constraint
class (Category k) => Cartesian k where

  --  Tensor introduction.
  (&&&) :: forall x y z. (Object k x, Object k y, Object k z) => k x y -> k x z -> k x (Tensor y z)

  -- | Left tensor eliminator.
  exl :: forall x y. (Object k x, Object k y) => k (Tensor x y) x

  -- | Right tensor eliminator.
  exr :: forall x y. (Object k x, Object k y) => k (Tensor x y) y

  -- | Evidence that a tensor of objects in this category is also an object in
  -- this category. It would be nice to express this as a quantified
  -- constraint, but because 'Object' is a type family, it can't be used in an
  -- instance head. We could also add it as a parameter on all the 'Category'
  -- type classes with a functional dependency, but that's a lot more visually
  -- noisy.
  tensor :: forall x y r. (Object k x, Object k y) => (Object k (Tensor x y) => r) -> r

-- | Swap the components of a tensor.
swap :: forall k x y. (Cartesian k, Object k x, Object k y) => k (Tensor x y) (Tensor y x)
swap = tensor @k @x @y (exr &&& exl)

-------------------------------------------------------------------------------

-- | A type-level representation of homsets within a category. Again, we
-- deliberately don't reuse something like (->) so we can differentate between
-- homs and, for example, objects-that-happen-to-be-functions.
type Hom :: Type -> Type -> Type
data Hom x y

-- | Categories with a notion of homomorphisms.
type Closed :: (Type -> Type -> Type) -> Constraint
class Cartesian k => Closed k where

  -- | An arrow from a homomorphism and a value in its domain to a value in its
  -- codomain. In more intuitive terms, this is function application.
  apply :: forall x y. (Object k x, Object k y) => k (Tensor (Hom x y) x) y
  apply = hom @k @x @y (uncurry id)

  -- | Currying of our arrows.
  curry :: (Object k x, Object k y, Object k z) => k (Tensor x y) z -> k x (Hom y z)

  -- | Uncurrying of our arrows.
  uncurry :: (Object k x, Object k y, Object k z) => k x (Hom y z) -> k (Tensor x y) z

  -- | Evidence that morphisms in this category are also objects in this
  -- category. See 'tensor' for a longer explanation of why this is necessary.
  hom :: (Object k x, Object k y) => (Object k (Hom x y) => r) -> r

-------------------------------------------------------------------------------

-- | A trivial constraint satisfied by all types.
type Trivial :: Type -> Constraint
class Trivial x
instance Trivial x

-- | Products of constraints.
type (&&) :: (Type -> Constraint) -> (Type -> Constraint) -> Type -> Constraint
class (c x, d x) => (c && d) x
instance (c x, d x) => (c && d) x
