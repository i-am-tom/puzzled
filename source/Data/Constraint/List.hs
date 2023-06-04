{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- |
-- Creating and projecting out of lists of constraints.
--
-- It's unfortunate that this module exists, but the tl;dr is explained here:
-- https://gitlab.haskell.org/ghc/ghc/-/issues/15636
--
-- When I create a type like 'Control.Category.Reify.Reify', I would like to be
-- able to write an 'Eq' instance like so:
--
--     instance (forall x. c x => Eq x) => Eq (Reify c) where ...
--
-- However, due to the behaviour described in the aforementioned ticket, this
-- is not currently possible. The workaround is to introduce a "transparent"
-- newtype around @x@ and instead write an instance like so:
--
--     instance (forall x. c x => Eq (Transparent x) => Eq (Reify c) where ...
--
-- Then, whenever I want to check any @c x => x@ for equality, I first wrap it
-- in the 'Transparent' constructor. However, this is pretty unsatisfactory: it
-- breaks stock deriving, and it doesn't always work for things like
-- 'Typeable', which seems to have some interesting special case behaviour:
--
--     instance (forall x. c x => Typeable x) => Eq (Reify c) -- Bad
--     instance (d ~ Typeable, forall x. c x => d x) => Eq (Reify c) -- Good?
--
-- Rather than spend more time trying to figure this out, this module exposes a
-- tensor type for constraints '(&&)' and a projection function 'infer'.
module Data.Constraint.List where

import Data.Kind (Constraint, Type)

-- | A value of type @Dict c x@ is evidence that @c x@ holds.
type Dict :: (k -> Constraint) -> k -> Type
data Dict c x where Dict :: (c x) => Dict c x

-- | The product of two constraints is the constraint that both constraints be
-- satisfied. This forms a 'Monoid'/'Control.Category.Category' with the unit
-- constraint @()@.
type (&&) :: (k -> Constraint) -> (k -> Constraint) -> (k -> Constraint)
class (c x, d x) => (c && d) x

instance (c x, d x) => (c && d) x

-- | A class whose instances witness the presence of a given constraint within
-- a @cons@-style product list of constraints.
type Elem :: (k -> Constraint) -> (k -> Constraint) -> Constraint
class Elem c cs where
  infer :: forall x. (cs x) => Dict c x

instance {-# OVERLAPPING #-} Elem c (c && cs) where
  infer = Dict

instance {-# OVERLAPPABLE #-} (Elem c cs) => Elem c (d && cs) where
  infer = infer @_ @_ @cs

-- | A convenience function for 'infer' that uses the given value as a proxy
-- for the type in the 'Dict'.
deduce :: forall c cs x. (Elem c cs, cs x) => x -> Dict c x
deduce _ = infer @_ @_ @cs
