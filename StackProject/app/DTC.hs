module DTC where

import Control.Monad

data Fix f = In (f (Fix f))
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Ord (f (Fix f)) => Ord (Fix f)

type Algebra f a = forall r. (r -> a) -> f r -> a

foldF :: (Functor f) => Algebra f a -> Fix f -> a
foldF alg (In f) = alg id $ fmap (foldF alg) f

infix 1 :<:
class f :<: g where
    inj :: f a -> g a
    proj :: g a -> Maybe (f a)

infixr 2 :+:
data (f :+: g) a = Inl (f a) | Inr (g a) deriving (Eq, Ord, Functor)

infixr 3 :*:
data (f :*: g) a = f a :*: g a deriving (Eq, Ord, Functor)

infixr 4 :.:
newtype (f :.: g) a = CIRC (f (g a)) deriving (Eq, Ord, Functor)

newtype KF b a = KF b deriving (Eq, Ord, Functor)
newtype KRec a = KRec a deriving (Eq, Ord, Functor)

type KID a = KF () a

foldCM :: (Monad m, Functor f) => (v (Fix (f :.: v)) -> m (Fix (f :.: v))) -> Algebra f (m a) -> Fix (f :.: v) -> m a
foldCM read alg (In (CIRC f)) = alg (foldCM read alg <=< read) f


instance (Functor f) => f :<: f where
    inj = id
    proj = Just

instance {-# OVERLAPPING #-} (Functor f, Functor g) => f :<: (f :+: g) where
    inj = Inl
    proj (Inl f) = Just f
    proj (Inr _) = Nothing

instance (Functor g, f :<: h) => f :<: (g :+: h) where
    inj = Inr . inj
    proj (Inl _) = Nothing
    proj (Inr f) = proj f


inject :: (f :<: g) => f (Fix g) -> Fix g
inject = In . inj

instance (Show a, Show (f a), Show (g a)) => Show ((f :+: g) a) where
    showsPrec d (Inl f) = showsPrec d f
    showsPrec d (Inr g) = showsPrec d g

instance (Show (f (Fix f))) => Show (Fix f) where
    showsPrec d (In f) = showsPrec d f

data Wit0 = Wit0
data Wit1 = Wit1
data Wit2 = Wit2

class (Functor f) => Functor0 f where
    intro0 :: f a
    elim0 :: b -> f a -> b

class (Functor f) => Functor1 f where
    intro1 :: a -> f a
    elim1 :: (a -> b) -> f a -> b

fst1 :: Functor1 f => f a -> a
fst1 = elim1 id

class (Functor f) => Functor2 f where
    intro2 :: a -> a -> f a
    elim2 :: (a -> a -> b) -> f a -> b