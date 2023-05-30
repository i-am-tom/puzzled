{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- A backtracking monad for primitive operations.
module Control.Monad.Branch
  ( BranchT (..),
    next,
    all,
  )
where

import Control.Applicative (Alternative)
import Control.Monad (MonadPlus)
import Control.Monad.Logic (LogicT, msplit, observeAllT, observeT)
import Control.Monad.Primitive (PrimMonad (..))
import Control.Monad.Trans.Class (lift)
import Data.Coerce (coerce)
import Data.Kind (Type)
import Prelude hiding (all)

-- | A wrapper around 'LogicT' that implements 'PrimMonad'. All we're doing is
-- avoiding an orphan instance.
type BranchT :: (Type -> Type) -> Type -> Type
newtype BranchT m x = BranchT {unBranchT :: LogicT m x}
  deriving newtype (Functor, Applicative, Monad, MonadFail)
  deriving newtype (Alternative, MonadPlus)

instance (PrimMonad m) => PrimMonad (BranchT m) where
  type PrimState (BranchT m) = PrimState m
  primitive = BranchT . lift . primitive

-- | Get the next successful result, as well as a 'BranchT' that computes all
-- the remaining results.
next :: (MonadFail m) => BranchT m x -> m (Maybe (x, BranchT m x))
next = fmap coerce . observeT . msplit . unBranchT

-- | Get all successful results in the 'BranchT' computation.
all :: (Applicative m) => BranchT m x -> m [x]
all = observeAllT . unBranchT
