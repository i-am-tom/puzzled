{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

-- |
-- The category of reified category operations.
module Control.Category.Reify where

import Control.Category.Hierarchy
import Control.Category.Propagate (Propagate (choice, unify))
import Data.Kind (Constraint, Type)
import GHC.Show (showSpace)
import Type.Reflection (Typeable, eqTypeRep, typeRep, (:~~:) (HRefl))
import Prelude hiding ((.))

-- | A category that implements the hierarchy by reifying all functions as
-- constructors in this GADT. This is useful because we can use it to observe
-- the structure of a computation.
type Reify :: (Type -> Constraint) -> Type -> Type -> Type
data Reify c x y where
  -- Category
  Compose :: (Typeable y) => Reify c y z -> Reify c x y -> Reify c x z
  Identity :: Reify c x x
  -- Cartesian
  Fork :: Reify c x y -> Reify c x z -> Reify c x (Tensor y z)
  Exl :: Reify c (Tensor x y) x
  Exr :: Reify c (Tensor x y) y
  -- Closed
  Curry :: Reify c (Tensor x y) z -> Reify c x (Hom y z)
  Uncurry :: Reify c x (Hom y z) -> Reify c (Tensor x y) z
  -- Terminal
  Kill :: Reify c x Unit
  -- Constant
  Const :: (c x) => x -> Reify c Unit x
  -- Propagate
  Choice :: Reify c (Tensor x x) x
  Unify :: Reify c (Tensor x x) x

instance (forall e. (c e) => Eq (Ghost e)) => Eq (Reify c x y) where
  Compose fx (fy :: _ m) == Compose gx (gy :: _ n) =
    case typeRep @m `eqTypeRep` typeRep @n of
      Just HRefl -> fx == gx && fy == gy
      Nothing -> False
  Identity == Identity = True
  Fork x y == Fork z w = x == z && y == w
  Exl == Exl = True
  Exr == Exr = True
  Curry x == Curry y = x == y
  Uncurry x == Uncurry y = x == y
  Kill == Kill = True
  Const x == Const y = Ghost x == Ghost y
  Choice == Choice = True
  Unify == Unify = True
  _ == _ = False

instance (forall e. (c e) => Show (Ghost e)) => Show (Reify c x y) where
  showsPrec p (Compose f g) =
    showParen (p >= 11) $
      showString "Compose "
        . showsPrec 11 f
        . showSpace
        . showsPrec 11 g
  showsPrec _ Identity =
    showString "Identity"
  showsPrec p (Fork f g) =
    showParen (p >= 11) $
      showString "Fork"
        . showsPrec 11 f
        . showSpace
        . showsPrec 11 g
  showsPrec _ Exl = showString "Exl"
  showsPrec _ Exr = showString "Exr"
  showsPrec p (Curry f) =
    showParen (p >= 11) $
      showString "Curry "
        . showsPrec 11 f
  showsPrec p (Uncurry f) =
    showParen (p >= 11) $
      showString "Uncurry "
        . showsPrec 11 f
  showsPrec _ Kill = showString "Kill"
  showsPrec p (Const x) =
    showParen (p >= 11) $
      showString "Const "
        . showsPrec 11 (Ghost x)
  showsPrec _ Choice = showString "Choice"
  showsPrec _ Unify = showString "Unify"

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

---

-- | Because of the way quantified constraints works, we can't do the seemingly
-- obvious thing that is @forall x. c x => Eq x@ to say that our mystery @c@
-- implies 'Eq'. Instead, we have to say that it implies 'Eq' on some newtype,
-- and then use _that_ evidence to do what we want. This is a bit clunky, but
-- it works.
--
-- https://gitlab.haskell.org/ghc/ghc/-/issues/15636
type Ghost :: Type -> Type
newtype Ghost x = Ghost x
  deriving newtype (Eq, Ord, Show)
