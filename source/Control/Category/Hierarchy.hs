{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

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
    const_,
  )
where

import Control.Arrow (Kleisli)
import Control.Category qualified as Base
import Data.Boring (Absurd (absurd))
import Data.Constraint.Extra (All, Trivial)
import Data.Kind (Constraint, Type)
import Prelude hiding (const, curry, id, uncurry, (.))

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
  id :: forall x. (Object k x) => k x x

  -- | Composition of morphisms.
  (.) :: forall x y z. (All (Object k) '[x, y, z]) => k y z -> k x y -> k x z

instance Category (->) where
  id = Base.id
  (.) = (Base..)

instance (Monad m) => Category (Kleisli m) where
  id = Base.id
  (.) = (Base..)

-------------------------------------------------------------------------------

-- | A type-level representation of tensors within a category. We deliberately
-- don't reuse something like (,) so we can differentiate between tensors and,
-- for example, objects-that-happen-to-be-tuples.
type Tensor :: Type -> Type -> Type
data Tensor x y deriving stock (Eq, Ord, Show)

instance Absurd (Tensor x y) where
  absurd = \case {}

-- | Categories with a notion of products (tensors).
type Cartesian :: (Type -> Type -> Type) -> Constraint
class (Category k) => Cartesian k where
  --  Tensor introduction.
  (&&&) :: forall x y z. (All (Object k) '[x, y, z, Tensor y z]) => k x y -> k x z -> k x (Tensor y z)

  -- | Left tensor eliminator.
  exl :: forall x y. (All (Object k) '[x, y]) => k (Tensor x y) x

  -- | Right tensor eliminator.
  exr :: forall x y. (All (Object k) '[x, y]) => k (Tensor x y) y

-- | Swap the components of a tensor.
swap :: (Cartesian k, All (Object k) '[x, y, Tensor x y, Tensor y x]) => k (Tensor x y) (Tensor y x)
swap = exr &&& exl

-------------------------------------------------------------------------------

-- | A type-level representation of homsets within a category. Again, we
-- deliberately don't reuse something like (->) so we can differentate between
-- homs and, for example, objects-that-happen-to-be-functions.
type Hom :: Type -> Type -> Type
data Hom x y deriving stock (Eq, Ord, Show)

instance Absurd (Hom x y) where
  absurd = \case {}

-- | Categories with a notion of homomorphisms.
type Closed :: (Type -> Type -> Type) -> Constraint
class (Cartesian k) => Closed k where
  -- | An arrow from a homomorphism and a value in its domain to a value in its
  -- codomain. In more intuitive terms, this is function application.
  apply :: forall x y. (All (Object k) '[x, y, Hom x y]) => k (Tensor (Hom x y) x) y
  apply = uncurry id

  -- | Currying of our arrows.
  curry :: All (Object k) '[x, y, z] => k (Tensor x y) z -> k x (Hom y z)

  -- | Uncurrying of our arrows.
  uncurry :: All (Object k) '[x, y, z] => k x (Hom y z) -> k (Tensor x y) z

-------------------------------------------------------------------------------

-- | A type-level representation of terminal objects within a category. See
-- 'Tensor' and 'Hom' for more information as to why we don't use '()'.
type Unit :: Type
data Unit deriving stock (Eq, Ord, Show)

instance Absurd Unit where
  absurd = \case {}

-- | Categories with a terminal object.
type Terminal :: (Type -> Type -> Type) -> Constraint
class (Category k) => Terminal k where
  -- | An arrow to the terminal object.
  kill :: (Object k x) => k x Unit

-------------------------------------------------------------------------------

-- | A class for mapping values from Hask into the given category.
type Const :: (Type -> Type -> Type) -> Type -> Constraint
class (Terminal k) => Const k x where
  -- | Lift a value into the category as an arrow from 'Unit'.
  const :: (Object k x) => x -> k Unit x

-- | Like 'const' but with an unrestricted domain.
const_ :: (Const k x, All (Object k) '[i, x, Unit]) => x -> k i x
const_ x = const x . kill
