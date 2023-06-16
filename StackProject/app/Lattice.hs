module Lattice where

import DTC

class Lattice a where
    (/\) :: a -> a -> a
    (\/) :: a -> a -> a

class (Lattice a) => BoundedJoinSemilattice a where
    top :: a


data Top a = Top deriving (Show, Eq, Ord, Functor)
data Bot a = Bot deriving (Show, Eq, Ord, Functor)

type TB f = Top :+: Bot :+: f 

topp :: (Functor f) => Fix (TB f) 
topp = inject Top

pattern Elem x = Inr (Inr x)
pattern TTOP = Inl Top
pattern TBOT = Inr (Inl Bot)

instance (
      Functor f
    , Functor g
    , Lattice ((TB f) a)
    , Lattice ((TB g) a)) => 
    Lattice ((TB (f :+: g)) a) where
    (Elem (Inl f1)) /\ (Elem (Inl f2)) = case (inj f1 /\ inj f2) of
        (TBOT) -> inj Bot
        (TTOP) -> error "meeting two concrete functors should never return a top level top! (has to have at least top level constructor)"
        (Elem ff) -> Elem ff

    {-}
    (Inr g1) /\ (Inr g2) = case (g1 /\ g2) of
        (proj -> Just Bot) -> inj Bot
        ff -> Inr ff
    _ /\ _ = inj Bot

    (Inl f1) \/ (Inl f2) = case (f1 \/ f2) of
        (proj -> Just Bot) -> inj Bot --Maybe should never happen
        ff -> Inl ff
    (Inr g1) \/ (Inr g2) = case (g1 \/ g2) of
        (proj -> Just Bot) -> inj Bot
        ff -> Inr ff
    _ \/ _ = inj Top
    -}

instance (Lattice (f a), Lattice (g a)) => Lattice ((f :*: g) a) where
    (f1 :*: g1) /\ (f2 :*: g2) = f1 /\ f2 :*: g1 /\ g2

    (f1 :*: g1) \/ (f2 :*: g2) = f1 \/ f2 :*: g1 \/ g2

instance (Lattice b) => Lattice (KF b a) where
    (KF x) /\ (KF y) = KF (x /\ y)
    (KF x) \/ (KF y) = KF (x \/ y)

instance (Lattice a) => Lattice (KRec a) where
    (KRec x) /\ (KRec y) = KRec (x /\ y)
    (KRec x) \/ (KRec y) = KRec (x \/ y)

instance (Lattice (f a), Top :<: f) => BoundedJoinSemilattice (f a) where
    top = inj Top