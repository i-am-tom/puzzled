{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- The category of reified category operations.
module Control.Category.Reify
  ( Reify (..),
    Void,
  )
where

import Data.Tuple (Solo (..))
import Control.Category.Eq (HEq ((===)))
import Control.Category.Hierarchy
import Control.Category.Propagate (Propagate (choice, unify))
import Data.Constraint.Extra (type (-->), type (&&))
import Data.Kind (Constraint, Type)
import GHC.Show (showSpace)
import Type.Reflection (Typeable, eqTypeRep, typeOf, (:~~:) (HRefl))
import Prelude hiding ((.))

-- | A category that implements the hierarchy by reifying all functions as
-- constructors in this GADT. This is useful because we can use it to observe
-- the structure of a computation.
type Reify :: (Type -> Constraint) -> ((Type -> Constraint) -> Type -> Type -> Type) -> Type -> Type -> Type
data Reify c k x y where
  -- Category
  Compose :: (c x, c y, c z) => Reify c k y z -> Reify c k x y -> Reify c k x z
  Identity :: (c x) => Reify c k x x
  -- Cartesian
  Fork :: (c x, c y, c z) => Reify c k x y -> Reify c k x z -> Reify c k x (Tensor y z)
  Exl :: (c x, c y) => Reify c k (Tensor x y) x
  Exr :: (c x, c y) => Reify c k (Tensor x y) y
  -- Closed
  Curry :: (c x, c y, c z) => Reify c k (Tensor x y) z -> Reify c k x (Hom y z)
  Uncurry :: (c x, c y, c z) => Reify c k x (Hom y z) -> Reify c k (Tensor x y) z
  -- Terminal
  Kill :: (c x) => Reify c k x Unit
  -- Constant
  Const :: (c x) => x -> Reify c k Unit x
  -- Propagate
  Choice :: (c x) => Reify c k (Tensor x x) x
  Unify :: (c x) => Reify c k (Tensor x x) x
  -- Extension
  Other :: k c x y -> Reify c k x y

instance (c --> (Eq && Typeable), HEq (k c)) => Eq (Reify c k x y) where
  (==) = (===)

instance (c --> (Eq && Typeable), HEq (k c)) => HEq (Reify c k) where
  (===) = \cases
    (Compose fx fy) (Compose gx gy) -> fx === gx && fy === gy
    Identity Identity -> True
    (Fork x y) (Fork z w) -> x === z && y === w
    Exl Exl -> True
    Exr Exr -> True
    (Curry x) (Curry y) -> x === y
    (Uncurry x) (Uncurry y) -> x === y
    Kill Kill -> True
    (Const x) (Const y) -> do
      let x' = Solo x
          y' = Solo y

      case eqTypeRep (typeOf x') (typeOf y') of
          Just HRefl -> x' == y'
          Nothing -> False
    Choice Choice -> True
    Unify Unify -> True
    (Other x) (Other y) -> x === y
    _ _ -> False

instance (c --> Show, forall a b. Show (k c a b)) => Show (Reify c k x y) where
  showsPrec p = \case
    Compose f g ->
      showParen (p >= 11) $
        showString "Compose "
          . showsPrec 11 f
          . showSpace
          . showsPrec 11 g
    Identity ->
      showString "Identity"
    Fork f g ->
      showParen (p >= 11) $
        showString "Fork"
          . showsPrec 11 f
          . showSpace
          . showsPrec 11 g
    Exl -> showString "Exl"
    Exr -> showString "Exr"
    Curry f ->
      showParen (p >= 11) $
        showString "Curry "
          . showsPrec 11 f
    Uncurry f ->
      showParen (p >= 11) $
        showString "Uncurry "
          . showsPrec 11 f
    Kill -> showString "Kill"
    Const x ->
      showParen (p >= 11) $
        showString "Const "
          . showsPrec 11 (Solo x)
    Choice -> showString "Choice"
    Unify -> showString "Unify"
    Other x ->
      showParen (p >= 11) $
        showString "Other "
          . showsPrec 11 x

instance Category (Reify cs k) where
  type Object (Reify cs k) = cs

  (.) = Compose
  id = Identity

instance Cartesian (Reify cs k) where
  (&&&) = Fork
  exl = Exl
  exr = Exr

instance Closed (Reify cs k) where
  curry = Curry
  uncurry = Uncurry

instance Terminal (Reify cs k) where
  kill = Kill

instance (cs x) => Const (Reify cs k) x where
  const = Const

instance Propagate (Reify cs k) where
  choice = Choice
  unify = Unify

-- | A void category that can be used to instantiate a version of 'Reify' with
-- no extensions.
type Void :: (Type -> Constraint) -> Type -> Type -> Type
data Void c x y deriving stock (Eq, Ord, Show)

instance HEq (Void c) where
  (===) = \case {}
