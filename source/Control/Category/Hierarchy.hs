{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- |
-- A class hierarchy for various types of category.
module Control.Category.Hierarchy
  ( -- * Categories
    Category (..),

    -- * Cartesian Categories
    Cartesian (..),
    Tensor,
    swap,

    -- * Cartesian Closed Categories
    Closed (..),
    Hom,

    -- * Terminal Categories
    Terminal (..),
    Unit,

    -- * Lifting into Categories
    Const (..),

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

-- | Swap the components of a tensor.
swap :: (Cartesian k, Object k x, Object k y, Object k (Tensor x y)) => k (Tensor x y) (Tensor y x)
swap = exr &&& exl

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
  apply :: forall x y. (Object k x, Object k y, Object k (Hom x y)) => k (Tensor (Hom x y) x) y
  apply = uncurry id

  -- | Currying of our arrows.
  curry :: (Object k x, Object k y, Object k z) => k (Tensor x y) z -> k x (Hom y z)

  -- | Uncurrying of our arrows.
  uncurry :: (Object k x, Object k y, Object k z) => k x (Hom y z) -> k (Tensor x y) z

-------------------------------------------------------------------------------

-- | A type-level representation of terminal objects within a category. See
-- 'Tensor' and 'Hom' for more information as to why we don't use '()'.
type Unit :: Type
data Unit

-- | Categories with a terminal object.
type Terminal :: (Type -> Type -> Type) -> Constraint
class Category k => Terminal k where

  -- | An arrow to the terminal object.
  kill :: Object k x => k x Unit

-------------------------------------------------------------------------------

-- | A class for mapping values from Hask into the given category.
type Const :: (Type -> Type -> Type) -> Type -> Constraint
class Terminal k => Const k x where

  -- | Lift a value into the category as an arrow from 'Unit'.
  const :: Object k x => x -> k Unit x

-------------------------------------------------------------------------------

-- | A trivial constraint satisfied by all types.
type Trivial :: Type -> Constraint
class Trivial x
instance Trivial x

-- | Products of constraints.
type (&&) :: (Type -> Constraint) -> (Type -> Constraint) -> Type -> Constraint
class (c x, d x) => (c && d) x
instance (c x, d x) => (c && d) x
