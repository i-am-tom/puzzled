{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Main (main) where

import Control.Category (Category ((.), id), (<<<))
import Data.IORef (IORef)
import Data.Kind (Type)
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Prelude hiding (curry, fst, id, snd, uncurry)

class Category k => CCC k where
  type Unit   k :: Type
  type Tensor k :: Type -> Type -> Type
  type Hom    k :: Type -> Type -> Type

  curry   :: k (Tensor k a b) c -> k a (Hom k b c)
  uncurry :: k a (Hom k b c) -> k (Tensor k a b) c
  fork    :: k a c -> k a d -> k a (Tensor k c d)
  exl     :: k (Tensor k a b) a
  exr     :: k (Tensor k a b) b

instance CCC (->) where
  type Unit   (->) = ()
  type Hom    (->) = (->)
  type Tensor (->) = (,)

  curry f x y = f (x, y)
  uncurry f (x, y) = f x y
  fork f g x = (f x, g x)
  exl (x, _) = x
  exr (_, y) = y

liftCCC :: CCC k => k a b -> k i a -> k i b
liftCCC = (<<<)

fst :: CCC k => k a (Tensor k b c) -> k a b
fst = liftCCC exl

snd :: CCC k => k a (Tensor k b c) -> k a c
snd = liftCCC exr

app :: CCC k => k i (Hom k a b) -> k i a -> k i b
app f x = eval <<< fork f x

eval :: CCC k => k (Tensor k (Hom k a b) a) b
eval = uncurry id

class CCC k => Cast k x y where
  cast :: k x y

instance {-# OVERLAPPABLE #-} (CCC k, Cast k b a, Tensor k b i ~ t)
    => Cast k t a where
  cast = cast <<< exl

instance CCC k => Cast k a a where
  cast = id

type Name :: (Type -> Type -> Type) -> Type -> Type -> Type
type Name k i a = forall x. Cast k x (Tensor k i a) => k x a

lam :: forall k i a b. CCC k => (Name k i a -> k (Tensor k i a) b) -> k i (Hom k a b)
lam f = curry (f exr_)
  where
    exr_ :: Cast k x (Tensor k i a) => k x a
    exr_ = exr <<< cast @_ @_ @(Tensor k i a)

s :: CCC k => k i (Hom k (Hom k p (Hom k q r)) (Hom k (Hom k p q) (Hom k p r)))
s = lam \x -> lam \y -> lam \z -> app (app x z) (app y z)

swap :: CCC k => k i (Hom k (Tensor k d c) (Tensor k c d))
swap = lam \x -> fork (snd x) (fst x)

class CCC k => Propagate k where
  branch_ :: k (Tensor k x x) x
  equate_ :: k (Tensor k x x) (Unit k)
  lift    :: x -> k (Unit k) x
  not_    :: k x (Unit k)


solve :: [Bool] -> (forall k. Propagate k i o) -> i -> Maybe (o, forall k. Propagate k i o)
--        ^ Infinite list of boolean choices


-- x = y; x = 5; y = ?
-- x = { 1, 2 }; x = y; y = ?
-- (x = y) -> BOT?


branch :: Propagate k => k i x -> k i x -> k i x
branch this that = liftCCC branch_ (fork this that)

equate :: Propagate k => k i x -> k i x -> k i (Unit k)
equate this that = liftCCC equate_ (fork this that)

not :: Propagate k => k i x -> k i ()
not = liftCCC not_

ifThenElse p x y = branch (p >>> x) (not p >>> x)
split :: Propagate k => k i x -> k i (Maybe (x, k i x))

---

data Reified i o where
  Id      :: Reified i i
  Compose :: Reified m o -> Reified i m -> Reified i o
  Curry   :: Reified (a, b) c -> Reified a (b -> c)
  Uncurry :: Reified a (b -> c) -> Reified (a, b) c

  Fork :: Reified i a -> Reified i b -> Reified i (a, b)
  Exl  :: Reified (a, b) a
  Exr  :: Reified (a, b) b

  Branch  :: Reified (x, x) x
  Equate  :: Reified (x, x) ()
  Lift    :: x -> Reified () x

instance Category Reified where
  id = Id
  (.) = Compose

instance CCC Reified where
  type Hom Reified = (->)
  type Tensor Reified = (,)
  type Unit Reified = ()

  curry   = Curry
  uncurry = Uncurry
  fork    = Fork
  exl     = Exl
  exr     = Exr

instance Propagate Reified where
  branch_ = Branch
  equate_ = Equate
  lift    = Lift

