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
import Data.Constraint.List (Dict (Dict), Elem, deduce)
import Data.Kind (Constraint, Type)
import GHC.Show (showSpace)
import Type.Reflection (Typeable, eqTypeRep, typeOf, (:~~:) (HRefl))
import Prelude hiding ((.))

-- | A category that implements the hierarchy by reifying all functions as
-- constructors in this GADT. This is useful because we can use it to observe
-- the structure of a computation.
type Reify :: (Type -> Constraint) -> Type -> Type -> Type
data Reify c x y where
  -- Category
  Compose :: (c x, c y, c z) => Reify c y z -> Reify c x y -> Reify c x z
  Identity :: (c x) => Reify c x x
  -- Cartesian
  Fork :: (c x, c y, c z) => Reify c x y -> Reify c x z -> Reify c x (Tensor y z)
  Exl :: (c x, c y) => Reify c (Tensor x y) x
  Exr :: (c x, c y) => Reify c (Tensor x y) y
  -- Closed
  Curry :: (c x, c y, c z) => Reify c (Tensor x y) z -> Reify c x (Hom y z)
  Uncurry :: (c x, c y, c z) => Reify c x (Hom y z) -> Reify c (Tensor x y) z
  -- Terminal
  Kill :: (c x) => Reify c x Unit
  -- Constant
  Const :: (c x) => x -> Reify c Unit x
  -- Propagate
  Choice :: (c x) => Reify c (Tensor x x) x
  Unify :: (c x) => Reify c (Tensor x x) x

instance (Elem (Eq && Typeable) c) => Eq (Reify c x y) where
  (==) = go
    where
      go :: Reify c i j -> Reify c k l -> Bool
      go (Compose fx fy) (Compose gx gy) = go fx gx && go fy gy
      go (Identity) (Identity) = True
      go (Fork x y) (Fork z w) = go x z && go y w
      go (Exl) (Exl) = True
      go (Exr) (Exr) = True
      go (Curry x) (Curry y) = go x y
      go (Uncurry x) (Uncurry y) = go x y
      go (Kill) (Kill) = True
      go (Const x) (Const y)
        | Dict <- deduce @(Eq && Typeable) @c x,
          Dict <- deduce @(Eq && Typeable) @c y = do
            case eqTypeRep (typeOf x) (typeOf y) of
              Just HRefl -> x == y
              Nothing -> False
      go (Choice) (Choice) = True
      go (Unify) (Unify) = True
      go (_) (_) = False

instance (Elem Show c) => Show (Reify c x y) where
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
  showsPrec p (Const x)
    | Dict <- deduce @Show @c x =
        showParen (p >= 11) $
          showString "Const "
            . showsPrec 11 x
  showsPrec _ Choice = showString "Choice"
  showsPrec _ Unify = showString "Unify"

instance Category (Reify cs) where
  type Object (Reify cs) = cs

  (.) = Compose
  id = Identity

instance Cartesian (Reify cs) where
  (&&&) = Fork
  exl = Exl
  exr = Exr

instance Closed (Reify cs) where
  curry = Curry
  uncurry = Uncurry

instance Terminal (Reify cs) where
  kill = Kill

instance (cs x) => Const (Reify cs) x where
  const = Const

instance Propagate (Reify cs) where
  choice = Choice
  unify = Unify
