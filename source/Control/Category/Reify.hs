{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
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

import Control.Category.Hierarchy
import Control.Category.Propagate (Propagate (choice, unify))
import Data.Boring (Absurd (absurd))
import Data.Constraint.Extra (All, type (~>))
import Data.Hashable (Hashable (hashWithSalt))
import Data.Kind (Constraint, Type)
import Data.Tuple (Solo (..))
import GHC.Show (showSpace)
import Type.Reflection (Typeable, eqTypeRep, typeOf, (:~~:) (HRefl))
import Prelude hiding ((.))

-- | A category that implements the hierarchy by reifying all functions as
-- constructors in this GADT. This is useful because we can use it to observe
-- the structure of a computation.
type Reify :: (Type -> Constraint) -> (Type -> Type -> Type) -> Type -> Type -> Type
data Reify c k x y where
  -- Category
  Compose :: (All Typeable '[x, y, z]) => Reify c k y z -> Reify c k x y -> Reify c k x z
  Identity :: (Typeable x) => Reify c k x x
  -- Cartesian
  Fork :: (All Typeable '[x, y, z]) => Reify c k x y -> Reify c k x z -> Reify c k x (Tensor y z)
  Exl :: (All Typeable '[x, y]) => Reify c k (Tensor x y) x
  Exr :: (All Typeable '[x, y]) => Reify c k (Tensor x y) y
  -- Closed
  Curry :: (All Typeable '[x, y, z]) => Reify c k (Tensor x y) z -> Reify c k x (Hom y z)
  Uncurry :: (All Typeable '[x, y, z]) => Reify c k x (Hom y z) -> Reify c k (Tensor x y) z
  -- Terminal
  Kill :: (Typeable x) => Reify c k x Unit
  -- Constant
  Const :: (c x) => x -> Reify c k y x
  -- Propagate
  Choice :: (Typeable x) => Reify c k (Tensor x x) x
  Unify :: (Typeable x) => Reify c k (Tensor x x) x
  -- Extension
  Other :: k x y -> Reify c k x y

instance
  (c ~> Eq, forall a b. Eq (k a b), Typeable k, Typeable c) =>
  Eq (Reify c k x y)
  where
  xs == ys = case (xs, ys) of
    (Compose fx fy, Compose gx gy) ->
      case eqTypeRep (typeOf fx) (typeOf gx) of
        Just HRefl -> fx == gx && fy == gy
        Nothing -> False
    (Identity, Identity) ->
      True
    (Fork x y, Fork z w) ->
      x == z && y == w
    (Exl, Exl) ->
      True
    (Exr, Exr) ->
      True
    (Curry x, Curry y) ->
      x == y
    (Uncurry x, Uncurry y) ->
      x == y
    (Kill, Kill) ->
      True
    (Const x, Const y) ->
      Solo x == Solo y
    (Choice, Choice) ->
      True
    (Unify, Unify) ->
      True
    (Other x, Other y) ->
      x == y
    _ ->
      False

instance
  (c ~> Eq, c ~> Hashable, forall a b. Hashable (k a b), Typeable k, Typeable c) =>
  Hashable (Reify c k x y)
  where
  hashWithSalt salt = \case
    Compose f g -> salt `hashWithSalt` (0 :: Int) `hashWithSalt` f `hashWithSalt` g
    Identity -> salt `hashWithSalt` (1 :: Int)
    Fork f g -> salt `hashWithSalt` (2 :: Int) `hashWithSalt` f `hashWithSalt` g
    Exl -> salt `hashWithSalt` (3 :: Int)
    Exr -> salt `hashWithSalt` (4 :: Int)
    Curry f -> salt `hashWithSalt` (5 :: Int) `hashWithSalt` f
    Uncurry f -> salt `hashWithSalt` (6 :: Int) `hashWithSalt` f
    Kill -> salt `hashWithSalt` (7 :: Int)
    Const x -> salt `hashWithSalt` (8 :: Int) `hashWithSalt` Solo x
    Choice -> salt `hashWithSalt` (9 :: Int)
    Unify -> salt `hashWithSalt` (10 :: Int)
    Other k -> salt `hashWithSalt` (11 :: Int) `hashWithSalt` k

instance
  (c ~> Show, forall a b. Show (k a b)) =>
  Show (Reify c k x y)
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
    Const x ->
      showParen (p >= 11) $
        showString "Const "
          . showsPrec 11 (Solo x)
    Choice -> showString "Choice"
    Unify -> showString "Unify"
    Other k ->
      showParen (p >= 11) $
        showString "Other "
          . showsPrec 11 k

instance Category (Reify c k) where
  type Object (Reify c k) = Typeable

  (.) = Compose
  id = Identity

instance Cartesian (Reify c k) where
  (&&&) = Fork
  exl = Exl
  exr = Exr

instance Closed (Reify c k) where
  curry = Curry
  uncurry = Uncurry

instance Terminal (Reify c k) where
  kill = Kill

instance (c x) => Const (Reify c k) x where
  const = Const

instance Propagate (Reify c k) where
  choice = Choice
  unify = Unify

-- | A void category that can be used to instantiate a version of 'Reify' with
-- no extensions.
type Void :: Type -> Type -> Type
data Void x y deriving stock (Eq, Ord, Show)

instance Absurd (Void x y) where
  absurd = \case {}
