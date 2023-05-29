{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- A backtracking monad for primitive operations.
module Control.Monad.Branch
  ( BranchT (..),
  )
where

import Control.Applicative (Alternative)
import Control.Monad (MonadPlus)
import Control.Monad.Logic (LogicT)
import Control.Monad.Primitive (PrimMonad (..))
import Control.Monad.Trans.Class (lift)
import Data.Kind (Type)

-- | A wrapper around 'LogicT' that implements 'PrimMonad'. All we're doing is
-- avoiding an orphan instance.
type BranchT :: (Type -> Type) -> Type -> Type
newtype BranchT m x = BranchT {unBranchT :: LogicT m x}
  deriving newtype (Functor, Applicative, Monad, MonadFail)
  deriving newtype (Alternative, MonadPlus)

instance (PrimMonad m) => PrimMonad (BranchT m) where
  type PrimState (BranchT m) = PrimState m
  primitive = BranchT . lift . primitive
