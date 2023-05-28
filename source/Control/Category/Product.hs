{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}

-- | Products of categories.
module Control.Category.Product where

import Control.Category.Hierarchy
import Data.Kind (Type)
import Prelude hiding (curry, id, uncurry, (.))

-- | A product of two categories is made up of two arrows for different
-- categories with common domain and codomain types. Rather than interpreting a
-- program twice, this allows us to produce two interpretations of the same
-- program simultaneously.
type Product :: (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type
newtype Product f g x y = Product_ {tuple :: (f x y, g x y)}
  deriving stock (Eq, Ord, Show)

-- | Syntactic sugar over the tuple within 'Product'.
pattern Product :: f x y -> g x y -> Product f g x y
pattern Product x y = Product_ {tuple = (x, y)}

{-# COMPLETE Product #-}

instance (Category f, Category g) => Category (Product f g) where
  type Object (Product f g) = Object f && Object g

  Product fx fy . Product gx gy =
    Product (fx . gx) (fy . gy)

  id = Product id id

instance (Cartesian f, Cartesian g) => Cartesian (Product f g) where
  exl = Product exl exl
  exr = Product exr exr

  Product fx fy &&& Product gx gy =
    Product (fx &&& gx) (fy &&& gy)

instance (Closed f, Closed g) => Closed (Product f g) where
  curry (Product f g) = Product (curry f) (curry g)
  uncurry (Product f g) = Product (uncurry f) (uncurry g)
