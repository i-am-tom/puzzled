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
  )
where

import Control.Category.Hierarchy
import Control.Category.Propagate (Propagate (choice, unify))
import Data.Constraint.Extra (type (-->))
import Data.Kind (Constraint, Type)
import Data.Tuple (Solo (..))
import GHC.Show (showSpace)
import Type.Reflection (Typeable, eqTypeRep, typeOf, (:~~:) (HRefl))
import Prelude hiding ((.))

-- | A category that implements the hierarchy by reifying all functions as
-- constructors in this GADT. This is useful because we can use it to observe
-- the structure of a computation.
type Reify :: (Type -> Constraint) -> Type -> Type -> Type
data Reify c x y where
  -- Category
  Compose :: (Typeable x, Typeable y, Typeable z) => Reify c y z -> Reify c x y -> Reify c x z
  Identity :: (Typeable x) => Reify c x x
  -- Cartesian
  Fork :: (Typeable x, Typeable y, Typeable z) => Reify c x y -> Reify c x z -> Reify c x (Tensor y z)
  Exl :: (Typeable x, Typeable y) => Reify c (Tensor x y) x
  Exr :: (Typeable x, Typeable y) => Reify c (Tensor x y) y
  -- Closed
  Curry :: (Typeable x, Typeable y, Typeable z) => Reify c (Tensor x y) z -> Reify c x (Hom y z)
  Uncurry :: (Typeable x, Typeable y, Typeable z) => Reify c x (Hom y z) -> Reify c (Tensor x y) z
  -- Terminal
  Kill :: (Typeable x) => Reify c x Unit
  -- Constant
  Const :: (c x) => x -> Reify c y x
  -- Propagate
  Choice :: (Typeable x) => Reify c (Tensor x x) x
  Unify :: (Typeable x) => Reify c (Tensor x x) x

instance (c --> Eq, Typeable c) => Eq (Reify c x y) where
  (==) = \cases
    (Compose fx fy) (Compose gx gy) ->
      case eqTypeRep (typeOf fx) (typeOf gx) of
        Just HRefl -> fx == gx && fy == gy
        Nothing -> False
    Identity Identity -> True
    (Fork x y) (Fork z w) -> x == z && y == w
    Exl Exl -> True
    Exr Exr -> True
    (Curry x) (Curry y) -> x == y
    (Uncurry x) (Uncurry y) -> x == y
    Kill Kill -> True
    (Const x) (Const y) -> Solo x == Solo y
    Choice Choice -> True
    Unify Unify -> True
    _ _ -> False

instance (c --> Show) => Show (Reify c x y) where
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

instance Category (Reify c) where
  type Object (Reify c) = Typeable

  (.) = Compose
  id = Identity

instance Cartesian (Reify c) where
  (&&&) = Fork
  exl = Exl
  exr = Exr

instance Closed (Reify c) where
  curry = Curry
  uncurry = Uncurry

instance Terminal (Reify c) where
  kill = Kill

instance (c x) => Const (Reify c) x where
  const = Const

instance Propagate (Reify c) where
  choice = Choice
  unify = Unify
