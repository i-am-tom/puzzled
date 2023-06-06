{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Arrows _within_ some 'Applicative' context.
module Control.Category.Lifted
  ( Lifted (..),
  )
where

import Control.Applicative (liftA2)
import Control.Category.Hierarchy
import Control.Category.Propagate (Propagate (choice, unify))
import Data.Kind (Type)
import Prelude hiding (const, curry, id, uncurry, (.))

-- | Arrows in @k@ within some 'Applicative' context. All class instances hold
-- for any 'Applicative' @m@.
type Lifted :: (Type -> Type -> Type) -> (Type -> Type) -> Type -> Type -> Type
newtype Lifted k m x y = Lifted (m (k x y))

instance (Category k, Applicative m) => Category (Lifted k m) where
  type Object (Lifted k m) = Object k

  Lifted f . Lifted g = Lifted (liftA2 (.) f g)
  id = Lifted (pure id)

instance (Cartesian k, Applicative m) => Cartesian (Lifted k m) where
  Lifted f &&& Lifted g = Lifted (liftA2 (&&&) f g)

  exl = Lifted (pure exl)
  exr = Lifted (pure exr)

instance (Closed k, Applicative m) => Closed (Lifted k m) where
  curry (Lifted f) = Lifted (fmap curry f)
  uncurry (Lifted f) = Lifted (fmap uncurry f)

instance (Terminal k, Applicative m) => Terminal (Lifted k m) where
  kill = Lifted (pure kill)

instance (Const k x, Applicative m) => Const (Lifted k m) x where
  const = Lifted . pure . const

instance (Propagate k, Applicative m) => Propagate (Lifted k m) where
  choice = Lifted (pure choice)
  unify = Lifted (pure unify)
