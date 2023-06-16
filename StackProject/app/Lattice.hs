module Lattice where

import DTC
import Lambda

class Lattice a where
    (/\) :: a -> a -> a
    (\/) :: a -> a -> a

class (Lattice a) => BoundedJoinSemilattice a where
    top :: a

class (Lattice a) => BoundedMeetSemilattice a where
    bot :: a

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
    , Lattice (TB f a)
    , Lattice (TB g a)) => 
    Lattice (TB (f :+: g) a) where
    (Elem (Inl f1)) /\ (Elem (Inl f2)) = case (inj f1 /\ inj f2) of
        (TBOT) -> inj Bot
        (TTOP) -> error "meeting two concrete functors should never return a top level top! (has to have at least top level constructor)"
        (Elem ff) -> Elem ff
    (Elem (Inl g1)) /\ (Elem (Inl g2)) = case (inj g1 /\ inj g2) of
        (TBOT) -> inj Bot
        (TTOP) -> error "meeting two concrete functors should never return a top level top! (has to have at least top level constructor)"
        (Elem ff) -> Elem ff
    _ /\ _ = inj Bot

    (Elem (Inl f1)) \/ (Elem (Inl f2)) = case (inj f1 \/ inj f2) of
        (TBOT) -> error "joining two concrete functors should never return a top level bot! (has to have at least top level constructor)"
        (TTOP) -> inj Top
        (Elem ff) -> Elem ff
    (Elem (Inl g1)) \/ (Elem (Inl g2)) = case (inj g1 \/ inj g2) of
        (TBOT) -> error "joining two concrete functors should never return a top level bot! (has to have at least top level constructor)"
        (TTOP) -> inj Top
        (Elem ff) -> Elem ff
    _ \/ _ = inj Top

instance (Functor f, Functor g, Lattice (TB f a), Lattice (TB g a)) => Lattice (TB (f :*: g) a) where
    TTOP /\ x = x
    x /\ TTOP = x
    TBOT /\ _ = TBOT
    _ /\ TBOT = TBOT
    (Elem (f1 :*: g1)) /\ (Elem (f2 :*: g2)) = case (inj @f @(TB f) f1 /\ inj f2, inj @g @(TB g) g1 /\ inj g2) of
        (TBOT, _) -> TBOT
        (_, TBOT) -> TBOT
        (Elem ff, Elem gg)  -> inj $ ff :*: gg

    TTOP \/ _ = TTOP
    _ \/ TTOP = TTOP
    TBOT \/ x = x
    x \/ TBOT = x
    (Elem (f1 :*: g1)) \/ (Elem (f2 :*: g2)) = case (inj @f @(TB f) f1 \/ inj f2, inj @g @(TB g) g1 \/ inj g2) of
        (TBOT, _) -> TBOT
        (_, TBOT) -> TBOT
        (Elem ff, Elem gg)  -> inj $ ff :*: gg

--TODO: Does not propagate bot upwards!
instance (Eq b, BoundedMeetSemilattice b) => Lattice (TB (KF b) a) where
    TTOP /\ x = x
    x /\ TTOP = x
    TBOT /\ _ = TBOT
    _ /\ TBOT = TBOT
    (Elem (KF x)) /\ (Elem (KF y))
        | (x /\ y) == bot = TBOT
        | otherwise = inj $ KF (x /\ y)

    TTOP \/ _ = TTOP
    _ \/ TTOP = TTOP
    TBOT \/ x = x
    x \/ TBOT = x
    (Elem (KF x)) \/ (Elem (KF y))
        | (x \/ y) == bot = TBOT
        | otherwise = inj $ KF (x \/ y)

--TODO: Does not propagate bot upwards!
instance (Eq a, BoundedMeetSemilattice a) => Lattice (TB KRec a) where
    TTOP /\ x = x
    x /\ TTOP = x
    TBOT /\ _ = TBOT
    _ /\ TBOT = TBOT
    (Elem (KRec x)) /\ (Elem (KRec y))
        | (x /\ y) == bot = TBOT
        | otherwise = inj $ KRec (x /\ y)

    TTOP \/ _ = TTOP
    _ \/ TTOP = TTOP
    TBOT \/ x = x
    x \/ TBOT = x
    (Elem (KRec x)) \/ (Elem (KRec y))
        | (x \/ y) == bot = TBOT
        | otherwise = inj $ KRec (x \/ y)

instance (Lattice (f a), Top :<: f) => BoundedJoinSemilattice (f a) where
    top = inj Top

instance (Lattice (f a), Bot :<: f) => BoundedMeetSemilattice (f a) where
    bot = inj Bot
