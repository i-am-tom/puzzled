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

stdmeet :: (f a -> f a -> TB f a) -> TB f a -> TB f a -> TB f a
stdmeet _ TTOP x = x
stdmeet _ x TTOP = x
stdmeet _ TBOT _ = TBOT
stdmeet _ _ TBOT = TBOT
stdmeet f (Elem x) (Elem y) = f x y

stdjoin :: (f a -> f a -> TB f a) -> TB f a -> TB f a -> TB f a
stdjoin _ TTOP _ = TTOP
stdjoin _ _ TTOP = TTOP
stdjoin _ TBOT x = x
stdjoin _ x TBOT = x
stdjoin f (Elem x) (Elem y) = f x y

--topp :: (Functor f) => Fix (TB f) 
--topp = In $ Inr $ Inl Bot

pattern Elem :: f a -> TB f a
pattern Elem x = Inr (Inr x)

pattern TTOP :: TB f a
pattern TTOP = Inl Top

pattern TBOT :: TB f a
pattern TBOT = Inr (Inl Bot)

instance (
      Functor f
    , Functor g
    , Lattice (TB f a)
    , Lattice (TB g a)) => 
    Lattice (TB (f :+: g) a) where
    (/\) = let 
        m (Inl f1) (Inl f2) = (case (inj f1 /\ inj f2) of
            (TBOT) -> inj Bot
            (TTOP) -> error "meeting two concrete functors should never return a top level top! (has to have at least top level constructor)"
            (Elem ff) -> Elem ff)
        m (Inr g1) (Inr g2) = case (inj g1 /\ inj g2) of
            (TBOT) -> inj Bot
            (TTOP) -> error "meeting two concrete functors should never return a top level top! (has to have at least top level constructor)"
            (Elem ff) -> Elem ff
        in stdmeet m

    (\/) = let 
        m (Inl f1) (Inl f2) = case (inj f1 \/ inj f2) of
            (TBOT) -> error "joining two concrete functors should never return a top level bot! (has to have at least top level constructor)"
            (TTOP) -> inj Top
            (Elem ff) -> Elem ff
        m (Inr g1) (Inr g2) = case (inj g1 \/ inj g2) of
            (TBOT) -> error "joining two concrete functors should never return a top level bot! (has to have at least top level constructor)"
            (TTOP) -> inj Top
            (Elem ff) -> Elem ff
        in stdjoin m

instance (Functor f, Lattice (TB v a), Lattice (TB f (TB v a))) => Lattice (TB (f :.: v) a) where
    (/\) = let
        m :: (f :.: v) a -> (f :.: v) a -> TB (f :.: v) a
        m (CIRC xf) (CIRC yf) = t xyf
            where 
                xyf = (Elem $ fmap Elem xf) /\ (Elem $ fmap Elem yf)
                t :: TB f (TB v a) -> TB (f :.: v) a
                t TTOP = TTOP
                t TBOT = TBOT
                t (Elem f) = k f
                    where 
                        --note: There can be no tops among the variables as they started as single elements
                        --TODO: maybe make lattice for TB (f :.: TB v) a? might be a tad annoying but prolly makes more sense here...
                        --Or maybe even...use the simpler version where you just go over the equality. Prolly we need the 
                        --unification interface for functors anyway...
                        k :: f (TB v a) -> TB f (v a)
                        k = _
        in stdmeet m

instance (Functor f, Functor g, Lattice (TB f a), Lattice (TB g a)) => Lattice (TB (f :*: g) a) where
    (/\) = let
        m (f1 :*: g1) (f2 :*: g2) = case (inj @f @(TB f) f1 /\ inj f2, inj @g @(TB g) g1 /\ inj g2) of
            (TBOT, _) -> TBOT
            (_, TBOT) -> TBOT
            (Elem ff, Elem gg)  -> inj $ ff :*: gg
        in stdmeet m

    (\/) = let
        m (f1 :*: g1) (f2 :*: g2) = case (inj @f @(TB f) f1 \/ inj f2, inj @g @(TB g) g1 \/ inj g2) of
            (TBOT, _) -> TBOT
            (_, TBOT) -> TBOT
            (Elem ff, Elem gg)  -> inj $ ff :*: gg
        in stdjoin m

--TODO: Does not propagate bot upwards!
instance (Eq b, BoundedMeetSemilattice b) => Lattice (TB (KF b) a) where
    (/\) = let
        m (KF x) (KF y)
            | (x /\ y) == bot = TBOT
            | otherwise = inj $ KF (x /\ y)
        in stdmeet m

    (\/) = let
        m (KF x) (KF y)
            | (x \/ y) == bot = TBOT
            | otherwise = inj $ KF (x \/ y)
        in stdjoin m

--TODO: Does not propagate bot upwards!
instance (Eq a, BoundedMeetSemilattice a) => Lattice (TB KRec a) where
    (/\) = let
        m (KRec x) (KRec y)
            | (x /\ y) == bot = TBOT
            | otherwise = inj $ KRec (x /\ y)
        in stdmeet m

    (\/) = let
        m (KRec x) (KRec y)
            | (x \/ y) == bot = TBOT
            | otherwise = inj $ KRec (x \/ y)
        in stdjoin m

instance (Lattice (f a), Top :<: f) => BoundedJoinSemilattice (f a) where
    top = inj Top

instance (Lattice (f a), Bot :<: f) => BoundedMeetSemilattice (f a) where
    bot = inj Bot

instance Lattice (TB DeBVarF a) where
    (/\) = let
        m (DeBVarF x) (DeBVarF y)
            | x /= y = TBOT
            | otherwise = inj $ DeBVarF x
        in stdmeet m

    (\/) = let
        m (DeBVarF x) (DeBVarF y)
            | x /= y = TTOP
            | otherwise = inj $ DeBVarF x
        in stdjoin m

instance (Eq a, BoundedMeetSemilattice a) => Lattice (TB LamF a) where
    (/\) = let 
        m :: LamF a -> LamF a -> TB LamF a
        m (LamF x) (LamF y) 
            | xy == bot = TBOT
            | otherwise = inj $ LamF xy
            where xy = x /\ y
        in stdmeet m
    
    (\/) = let 
        m :: LamF a -> LamF a -> TB LamF a
        m (LamF x) (LamF y) 
            | xy == bot = TBOT
            | otherwise = inj $ LamF xy
            where xy = x \/ y
        in stdjoin m

instance (Eq a, BoundedMeetSemilattice a) => Lattice (TB ApplF a) where
    (/\) = let
        m :: ApplF a -> ApplF a -> TB ApplF a
        m (ApplF x1 y1) (ApplF x2 y2)
            | xx == bot || yy == bot = TBOT
            | otherwise = inj $ ApplF xx yy
            where
                xx = x1 /\ x2
                yy = y1 /\ y2
        in stdmeet m

    (\/) = let
        m :: ApplF a -> ApplF a -> TB ApplF a
        m (ApplF x1 y1) (ApplF x2 y2)
            | xx == bot || yy == bot = TBOT
            | otherwise = inj $ ApplF xx yy
            where
                xx = x1 \/ x2
                yy = y1 \/ y2
        in stdjoin m