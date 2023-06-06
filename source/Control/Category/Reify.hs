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

import Control.Category.Eq (HEq ((===)), Heterogeneous (Heterogeneous))
import Control.Category.Hierarchy
import Control.Category.Propagate (Propagate (choice, unify))
import Data.Constraint.List (Dict (Dict), Elem, deduce)
import Data.Kind (Constraint, Type)
import GHC.Show (showSpace)
import Type.Reflection (Typeable, eqTypeRep, typeOf, (:~~:) (HRefl))
import Prelude hiding ((.))

-- | A category that implements the hierarchy by reifying all functions as
-- constructors in this GADT. This is useful because we can use it to observe
-- the structure of a computation.
type Reify :: (Type -> Constraint) -> ((Type -> Constraint) -> Type -> Type -> Type) -> (Type -> Type) -> Type -> Type -> Type
data Reify c k f x y where
  -- Category
  Compose :: (c x, c y, c z) => Reify c k f y z -> Reify c k f x y -> Reify c k f x z
  Identity :: (c x) => Reify c k f x x
  -- Cartesian
  Fork :: (c x, c y, c z) => Reify c k f x y -> Reify c k f x z -> Reify c k f x (Tensor y z)
  Exl :: (c x, c y) => Reify c k f (Tensor x y) x
  Exr :: (c x, c y) => Reify c k f (Tensor x y) y
  -- Closed
  Curry :: (c x, c y, c z) => Reify c k f (Tensor x y) z -> Reify c k f x (Hom y z)
  Uncurry :: (c x, c y, c z) => Reify c k f x (Hom y z) -> Reify c k f (Tensor x y) z
  -- Terminal
  Kill :: (c x) => Reify c k f x Unit
  -- Constant
  Const :: (c (f x)) => f x -> Reify c k f Unit x
  -- Propagate
  Choice :: (c x) => Reify c k f (Tensor x x) x
  Unify :: (c x) => Reify c k f (Tensor x x) x
  -- Extension
  Other :: k c x y -> Reify c k f x y

deriving via
  (Heterogeneous (Reify c k f) x y)
  instance
    (Elem (Eq && Typeable) c, HEq (k c)) =>
    Eq (Reify c k f x y)

instance (Elem (Eq && Typeable) c, HEq (k c)) => HEq (Reify c k f) where
  (===) = \cases
    (Compose fx fy) (Compose gx gy) -> fx === gx && fy === gy
    Identity Identity -> True
    (Fork x y) (Fork z w) -> x === z && y === w
    Exl Exl -> True
    Exr Exr -> True
    (Curry x) (Curry y) -> x === y
    (Uncurry x) (Uncurry y) -> x === y
    Kill Kill -> True
    (Const x) (Const y)
      | Dict <- deduce @(Eq && Typeable) @c x,
        Dict <- deduce @(Eq && Typeable) @c y -> do
          case eqTypeRep (typeOf x) (typeOf y) of
            Just HRefl -> x == y
            Nothing -> False
    Choice Choice -> True
    Unify Unify -> True
    (Other x) (Other y) -> x === y
    _ _ -> False

instance
  (Elem Show c, forall a b. Show (k c a b)) =>
  Show (Reify c k f x y)
  where
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
    Const x
      | Dict <- deduce @Show @c x ->
          showParen (p >= 11) $
            showString "Const "
              . showsPrec 11 x
    Choice -> showString "Choice"
    Unify -> showString "Unify"
    Other x ->
      showParen (p >= 11) $
        showString "Other "
          . showsPrec 11 x

instance Category (Reify cs k f) where
  type Object (Reify cs k f) = cs

  (.) = Compose
  id = Identity

instance Cartesian (Reify cs k f) where
  (&&&) = Fork
  exl = Exl
  exr = Exr

instance Closed (Reify cs k f) where
  curry = Curry
  uncurry = Uncurry

instance Terminal (Reify cs k f) where
  kill = Kill

instance (Applicative f, cs (f x)) => Const (Reify cs k f) x where
  const = Const . pure

instance Propagate (Reify cs k f) where
  choice = Choice
  unify = Unify

-- | A void category that can be used to instantiate a version of 'Reify' with
-- no extensions.
type Void :: (Type -> Constraint) -> Type -> Type -> Type
data Void c x y
