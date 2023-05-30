{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Propagator.Execute
  ( forwards,
    backwards,
    Value,
    create,
    unsafeRead,
    watch,
    write,
    Execute (Execute),
    Cell (..),
  )
where

import Control.Applicative (Alternative (empty, (<|>)), liftA2)
import Control.Arrow (Kleisli (Kleisli))
import Control.Category.Hierarchy
import Control.Category.Propagate (Propagate (..))
import Control.Monad (MonadPlus, join)
import Control.Monad.Primitive (PrimMonad)
import Data.Kind (Type)
import Data.Monoid.JoinSemilattice (JoinSemilattice (..), Merge (..))
import Data.Primitive.MutVar (newMutVar, readMutVar)
import Data.Primitive.MutVar.Rollback (Ref, atomicModifyMutVar)
import Prelude hiding (const, id, read, (.))

-- | Run an 'Execute' arrow with the given input, and return the output.
forwards :: (MonadPlus m, PrimMonad m, JoinSemilattice i) => Execute m i o -> i -> m o
forwards (Execute k) x = do
  input <- create x

  k (Object input) >>= \case
    Object ref -> unsafeRead ref
    Tensor _ _ -> empty
    Terminal -> empty
    Morphism _ -> empty

-- | Run an 'Execute' arrow with the given output, and return the input.
backwards :: (MonadPlus m, PrimMonad m, JoinSemilattice i) => Execute m i o -> o -> m i
backwards (Execute k) x = do
  input <- create mempty

  k (Object input) >>= \case
    Object ref -> write ref x *> unsafeRead input
    Tensor _ _ -> empty
    Terminal -> empty
    Morphism _ -> empty

---

-- | "Regular" (non-tensor, non-terminal, non-hom) values within our network
-- are stored in mutable variables. Over time, we may 'Merge' other values into
-- here, moving the result up the lattice.
type Value :: (Type -> Type) -> Type -> Type
newtype Value m x = Value (Ref m (x, m ()))
  deriving newtype (Eq)

-- | Create a new value in a 'Value' wrapper.
create :: (PrimMonad m) => x -> m (Value m x)
create x = fmap Value do
  newMutVar (x, pure ())

-- | Read the value within a 'Value' wrapper. This does not record provenance,
-- so this should not be used in any user code!
unsafeRead :: (PrimMonad m) => Value m x -> m x
unsafeRead (Value ref) = fmap fst (readMutVar ref)

-- | Attach a propagator to a 'Value' to fire whenever the value updates.
watch :: (MonadPlus m, PrimMonad m, JoinSemilattice x) => Value m x -> (x -> m ()) -> m ()
watch (Value ref) p = join $ atomicModifyMutVar ref \(x, ps) -> ((x, p' *> ps), p')
  where
    p' = readMutVar ref >>= p . fst

-- | Write information to a 'Value', firing its propagators if the value
-- changes.
write :: (MonadPlus m, PrimMonad m, JoinSemilattice x) => Value m x -> x -> m ()
write (Value ref) x = join do
  atomicModifyMutVar ref \(y, ps) ->
    case x <~ y of
      Changed z -> ((z, ps), ps)
      Unchanged _ -> ((x, ps), pure ())

---

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
  Morphism :: (Cell m x -> m (Cell m y)) -> Cell m (Hom x y)

-- | Eliminator for tensors.
tensor :: (PrimMonad m) => (Cell m x -> Cell m y -> m r) -> Cell m (Tensor x y) -> m r
tensor f = \case
  Object v -> unsafeRead v >>= \case {}
  Tensor x y -> f x y

-- | Eliminator for morphisms.
morphism :: (PrimMonad m) => ((Cell m x -> m (Cell m y)) -> m r) -> Cell m (Hom x y) -> m r
morphism f = \case
  Object v -> unsafeRead v >>= \case {}
  Morphism k -> f k

-- | A category in which propagator computations can be executed over mutable
-- variables. We 'unify' via the 'JoinSemilattice' instance of the values.
type Execute :: (Type -> Type) -> Type -> Type -> Type
newtype Execute m i o = Execute_ (Kleisli m (Cell m i) (Cell m o))

{-# COMPLETE Execute #-}

pattern Execute :: (Cell m i -> m (Cell m o)) -> Execute m i o
pattern Execute k = Execute_ (Kleisli k)

instance (Monad m) => Category (Execute m) where
  Execute_ f . Execute_ g = Execute_ (f . g)
  id = Execute_ id

instance (PrimMonad m) => Cartesian (Execute m) where
  Execute f &&& Execute g = Execute \x ->
    liftA2 Tensor (f x) (g x)

  exl = Execute (tensor \x _ -> pure x)
  exr = Execute (tensor \_ y -> pure y)

instance (PrimMonad m) => Closed (Execute m) where
  curry (Execute f) = Execute \x ->
    pure $ Morphism \y -> f (Tensor x y)

  uncurry (Execute f) = Execute do
    tensor \x y -> f x >>= morphism \k -> k y

instance (Monad m) => Terminal (Execute m) where
  kill = Execute \_ -> pure Terminal

instance (PrimMonad m, JoinSemilattice x) => Const (Execute m) x where
  const x = Execute \_ -> fmap Object (create x)

instance (MonadFail m, MonadPlus m, PrimMonad m) => Propagate (Execute m) where
  choice = Execute (tensor \x y -> pure x <|> pure y)
  unify = Execute (tensor \x y -> x <$ recurse x y)
    where
      recurse :: Cell m x -> Cell m x -> m ()
      recurse (Tensor x y) (Tensor z w) = recurse x z *> recurse y w
      recurse (Object one) (Object two) = watch one (write two) *> watch two (write one)
      recurse _ _ = fail "TODO: unify morphisms?"
