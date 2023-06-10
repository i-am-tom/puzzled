{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Propagator.Execute where

import Control.Applicative (empty, liftA2, (<|>))
import Control.Category.Hierarchy
import Control.Category.Propagate (Propagate (..))
import Control.Category.Reify (Reify (..))
import Control.Monad (MonadPlus)
import Control.Monad.Primitive (PrimMonad (PrimState), RealWorld)
import Data.Boring (absurd)
import Data.Constraint.Extra (type (&&))
import Data.Hashable (Hashable (hashWithSalt))
import Data.Kind (Type)
import Data.Monoid.JoinSemilattice (JoinSemilattice (..))
import Data.Semigroup (Arg (Arg))
import Prelude hiding (const, id, read, (.))
import Propagator.Cell (Value, create, unsafeRead, watch, write)
import Type.Reflection (Typeable)

-- | Run an 'Execute' arrow with the given input, and return the output.
forwards :: (MonadPlus m, PrimMonad m, PrimState m ~ RealWorld, JoinSemilattice i) => Execute m i o -> i -> m o
forwards k x = do
  input <- create x

  execute k (Object input) >>= \case
    Object ref -> unsafeRead ref
    Tensor _ _ -> empty
    Terminal -> empty
    Morphism _ -> empty

-- | Run an 'Execute' arrow with the given output, and return the input.
backwards :: (MonadPlus m, PrimMonad m, PrimState m ~ RealWorld, JoinSemilattice i) => Execute m i o -> o -> m i
backwards k x = do
  input <- create mempty

  execute k (Object input) >>= \case
    Object ref -> write ref x *> unsafeRead input
    Tensor _ _ -> empty
    Terminal -> empty
    Morphism _ -> empty

-- | Objects within the 'Execute' category.
type Cell :: (Type -> Type) -> Type -> Type
data Cell m x where
  -- | The terminal object.
  Terminal :: Cell m Unit
  -- | A "regular" mutable object.
  Object :: (JoinSemilattice x) => Value m x -> Cell m x
  -- | Tensors.
  Tensor :: Cell m x -> Cell m y -> Cell m (Tensor x y)
  -- | Homomorphisms.
  Morphism :: Execute m x y -> Cell m (Hom x y)

deriving stock instance (Typeable m) => Eq (Cell m x)

instance (Typeable m) => Hashable (Cell m x) where
  hashWithSalt salt = \case
    Terminal -> salt `hashWithSalt` (0 :: Int)
    Object (Arg i _) -> salt `hashWithSalt` (1 :: Int) `hashWithSalt` i
    Tensor x y -> salt `hashWithSalt` (2 :: Int) `hashWithSalt` x `hashWithSalt` y
    Morphism f -> salt `hashWithSalt` (3 :: Int) `hashWithSalt` f

tensor :: (PrimMonad m, PrimState m ~ RealWorld) => Cell m (Tensor x y) -> (Cell m x -> Cell m y -> m r) -> m r
tensor xs k = case xs of Tensor x y -> k x y; Object ref -> unsafeRead ref >>= absurd

morphism :: (PrimMonad m, PrimState m ~ RealWorld) => Cell m (Hom x y) -> (Execute m x y -> m r) -> m r
morphism xs k = case xs of Morphism f -> k f; Object ref -> unsafeRead ref >>= absurd

type Partial :: (Type -> Type) -> Type -> Type -> Type
data Partial m x y where
  Embed :: Cell m x -> Partial m Unit x

deriving stock instance (Typeable m) => Eq (Partial m x y)

instance (Typeable m) => Hashable (Partial m x y) where
  hashWithSalt salt (Embed x) = hashWithSalt salt x

type Execute :: (Type -> Type) -> Type -> Type -> Type
newtype Execute m x y = Execute (Reify (Eq && Hashable && JoinSemilattice && Show) (Partial m) x y)
  deriving newtype (Category, Cartesian, Closed, Eq, Hashable, Propagate, Terminal)

instance (Eq x, Hashable x, JoinSemilattice x, Show x) => Const (Execute m) x where
  const = Execute . const

embed :: Cell m x -> Execute m Unit x
embed = Execute . Other . Embed

embed_ :: (Typeable x, Typeable y) => Cell m x -> Execute m y x
embed_ x = embed x . kill

execute :: forall m i o. (MonadPlus m, PrimMonad m, PrimState m ~ RealWorld) => Execute m i o -> Cell m i -> m (Cell m o)
execute (Execute command) input = go input command
  where
    go :: Cell m x -> Reify (Eq && Hashable && JoinSemilattice && Show) (Partial m) x y -> m (Cell m y)
    go xs = \case
      Compose f g -> go xs g >>= \y -> go y f
      Identity -> pure xs
      Fork f g -> liftA2 Tensor (go xs f) (go xs g)
      Exl -> tensor xs \x _ -> pure x
      Exr -> tensor xs \_ y -> pure y
      Kill -> pure Terminal
      Const x -> fmap Object (create x)
      Curry f -> pure $ Morphism (Execute f . (embed_ xs &&& id))
      Uncurry f -> tensor xs \x y -> go x f >>= flip morphism \(Execute k) -> go y k
      Choice -> tensor xs \x y -> pure x <|> pure y
      Other (Embed ref) -> pure ref
      Unify -> tensor xs \x y -> do
        let recurse :: Cell m x -> Cell m x -> m ()
            recurse as bs = case (as, bs) of
              (Terminal, Terminal) ->
                pure ()
              (Morphism _, Morphism _) ->
                error "Unify morphisms?"
              (Object a, Object b) -> do
                watch a (write b)
                watch b (write a)
              (Tensor a b, Tensor c d) ->
                recurse a c *> recurse b d
              _ ->
                pure ()

        x <$ recurse x y
