{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}

-- | Category of linear operation sequences

module ConCat.Chain where

import Prelude hiding (id,(.),curry,uncurry)

import ConCat.Misc ((:*))
import qualified ConCat.Category as C
import ConCat.AltCat

infixr 5 :<
data Chain :: (* -> * -> *) -> (* -> * -> *) where
  Nil  :: Ok  k a => Chain k a a
  (:<) :: Ok3 k a b c => a `k` b -> Chain k b c -> Chain k a c

-- mapChain :: forall j k.
--             (forall a b.       j a b ->       k a b)
--          -> (forall a b. Chain j a b -> Chain k a b)
-- mapChain f = go
--  where
--    go :: forall a b. Chain j a b -> Chain k a b
--    go Nil         = Nil
--    go (op :< ops) = f op :< go ops

evalChain :: Category k => Chain k a b -> a `k` b
evalChain Nil          = id
evalChain (op :< rest) = evalChain rest . op

pureChain :: Ok2 k a b => a `k` b -> Chain k a b
pureChain f = f :< Nil

toList :: forall k z a b. (forall u v. (u `k` v) -> z) -> Chain k a b -> [z]
toList f = go
 where
   go :: Chain k p q -> [z]
   go Nil         = []
   go (op :< ops) = f op : go ops

instance Show2 k => Show (Chain k a b) where
  show = show . toList Exists2

instance Category (Chain k) where
  type Ok (Chain k) = Ok k
  id  = Nil
  (.) = flip (++*)

infixr 5 ++*
(++*) :: Ok3 k a b c => Chain k a b -> Chain k b c -> Chain k a c
(++*) Nil ops          = ops
(++*) (op :< ops) ops' = op :< (ops ++* ops')

-- We could reverse in toList or show instead of in (.)

instance AssociativePCat k => AssociativePCat (Chain k) where
  lassocP :: forall a b c. Ok3 k a b c => Chain k (a :* (b :* c)) ((a :* b) :* c)
  lassocP = pureChain lassocP
          <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
          <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
  rassocP :: forall a b c. Ok3 k a b c => Chain k ((a :* b) :* c) (a :* (b :* c))
  rassocP = pureChain rassocP
          <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
          <+ okProd @k @(a :* b) @c <+ okProd @k @a @b

instance BraidedPCat k => BraidedPCat (Chain k) where
  swapP :: forall a b. Ok2 k a b => Chain k (a :* b) (b :* a)
  swapP = swapP :< Nil
    <+ okProd @k @a @b <+ okProd @k @b @a

instance ProductCat k => ProductCat (Chain k) where
  exl :: forall a b. Ok2 k a b => Chain k (a :* b) a
  exr :: forall a b. Ok2 k a b => Chain k (a :* b) b
  dup :: forall a  . Ok  k a   => Chain k a (a :* a)
  exl = pureChain exl <+ okProd @k @a @b
  exr = pureChain exr <+ okProd @k @a @b
  dup = pureChain dup <+ okProd @k @a @a

instance (MonoidalPCat k, BraidedPCat k) => MonoidalPCat (Chain k) where
  first :: forall a b c. Ok3 k a b c => Chain k a c -> Chain k (a :* b) (c :* b)
  first Nil = Nil <+ okProd @k @a @b
  first (op :< ops) = firstCons op ops
   where
     firstCons :: forall x. Ok k x => (a `k` x) -> Chain k x c -> Chain k (a :* b) (c :* b)
     firstCons f fs = first f :< first fs
       <+ okProd @k @a @b <+ okProd @k @c @b <+ okProd @k @x @b
  second = secondFirst
  (***) = crossSecondFirst

instance TerminalCat k => TerminalCat (Chain k) where
  it = pureChain it

instance (BraidedPCat k, MProductCat k, TerminalCat k) => UnitCat (Chain k)
  
instance (OkProd k, NumCat k a) => NumCat (Chain k) a where
  negateC = pureChain negateC
  addC  = pureChain addC  <+ okProd @k @a @a
  subC  = pureChain subC  <+ okProd @k @a @a
  mulC  = pureChain mulC  <+ okProd @k @a @a
  powIC = pureChain powIC <+ okProd @k @a @Int

-- TODO: Many more instances

{--------------------------------------------------------------------
    Miscellany
--------------------------------------------------------------------}

data Exists2 k = forall a b. Exists2 (a `k` b)

instance Show2 k => Show (Exists2 k) where show (Exists2 f) = show2 f
