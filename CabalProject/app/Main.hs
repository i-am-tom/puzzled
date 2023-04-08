{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE Unsafe #-}

module Main (main) where

import Data.Kind (Type)
import Data.Unique (Unique)
import Prelude
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName (StableName, makeStableName)
import Type.Reflection ((:~~:) (HRefl), Typeable, eqTypeRep, typeOf)

type Expression :: Type -> Type
data Expression x where
  Free
    :: Unique
    -> Expression x

  Apply
    :: Typeable x
    => Expression (x -> y)
    -> Expression x
    -> Expression y

  Lambda
    :: StableName (Expression x -> Expression y)
    -> (Expression x -> Expression y)
    -> Expression (x -> y)

instance Eq (Expression x) where
  Free   x   == Free   y   = x == y
  Lambda s _ == Lambda t _ = s == t
  Apply  f x == Apply  g y
    = case eqTypeRep (typeOf x) (typeOf y) of
        Just HRefl -> f == g && x == y
        Nothing    -> False

  _ == _ = False

lam :: (Expression x -> Expression y) -> Expression (x -> y)
lam f = Lambda (unsafePerformIO (makeStableName f)) f

fix :: Expression ((Int -> Int) -> Int)
fix = lam \f -> Apply f (Apply fix f)

-- $> main
main :: IO ()
main = print $ fix == fix
