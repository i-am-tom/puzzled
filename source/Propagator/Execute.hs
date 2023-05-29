{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Propagator.Execute where

import Control.Applicative (liftA2)
import Control.Arrow (Kleisli (Kleisli))
import Control.Category.Hierarchy
import Control.Monad.Primitive (PrimMonad (PrimState))
import Data.Kind (Type)
import Data.Primitive.MutVar (MutVar, newMutVar, readMutVar)
import Prelude hiding ((.), id)

-- | "Regular" (non-tensor, non-terminal, non-hom) values within our network
-- are stored in mutable variables. Over time, we may 'Merge' other values into
-- here, moving the result up the lattice.
type Value :: (Type -> Type) -> Type -> Type
newtype Value m x = Value {ref :: MutVar (PrimState m) x}
  deriving newtype Eq

-- | Execute a function on the value within a 'Value' wrapper.
with :: PrimMonad m => Value m x -> (x -> m r) -> m r
with (Value ref) k = readMutVar ref >>= k

-- | Objects within the 'Execute' category.
type Cell :: (Type -> Type) -> Type -> Type
data Cell m x where
  -- | The terminal object.
  Terminal :: Cell m Unit
  -- | A "regular" mutable object.
  Object :: Value m x -> Cell m x
  -- | Tensors.
  Tensor :: Cell m x -> Cell m y -> Cell m (Tensor x y)
  -- | Homomorphisms.
  Morphism :: (Cell m x -> m (Cell m y)) -> Cell m (Hom x y)

-- | Eliminator for tensors.
tensor :: PrimMonad m => (Cell m x -> Cell m y -> m r) -> Cell m (Tensor x y) -> m r
tensor f = \case
  Object v -> with v \case {}
  Tensor x y -> f x y

-- | Eliminator for morphisms.
morphism :: PrimMonad m => ((Cell m x -> m (Cell m y)) -> m r) -> Cell m (Hom x y) -> m r
morphism f = \case
  Object v -> with v \case {}
  Morphism k -> f k

-- | A category in which propagator computations can be executed over mutable
-- variables. We 'unify' via the 'JoinSemilattice' instance of the values.
type Execute :: (Type -> Type) -> Type -> Type -> Type
newtype Execute m i o = Execute_ { execute :: Kleisli m (Cell m i) (Cell m o) }

{-# COMPLETE Execute #-}

pattern Execute :: (Cell m i -> m (Cell m o)) -> Execute m i o
pattern Execute k = Execute_ (Kleisli k)

instance Monad m => Category (Execute m) where
  Execute_ f . Execute_ g = Execute_ (f . g)
  id = Execute_ id

instance PrimMonad m => Cartesian (Execute m) where
  Execute f &&& Execute g = Execute \x ->
    liftA2 Tensor (f x) (g x)

  exl = Execute (tensor \x _ -> pure x)
  exr = Execute (tensor \_ y -> pure y)

instance PrimMonad m => Closed (Execute m) where
  curry (Execute f) = Execute \x ->
    pure $ Morphism \y -> f (Tensor x y)

  uncurry (Execute f) = Execute do
    tensor \x y -> f x >>= morphism \k -> k y

instance Monad m => Terminal (Execute m) where
  kill = Execute \_ -> pure Terminal

instance PrimMonad m => Const (Execute m) x where
  const x = Execute \_ -> fmap (Object . Value) (newMutVar x)
