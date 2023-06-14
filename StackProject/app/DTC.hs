module DTC where

data Fix f = In (f (Fix f))
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Ord (f (Fix f)) => Ord (Fix f)

type Algebra f a = forall r. (r -> a) -> f r -> a

foldF :: (Functor f) => Algebra f a -> Fix f -> a
foldF alg (In f) = alg id $ fmap (foldF alg) f

infix 1 :<:
class (Functor f, Functor g) => f :<: g where
    inj :: f a -> g a
    proj :: g a -> Maybe (f a)

infixr 2 :+:
data (f :+: g) a = Inl (f a) | Inr (g a) deriving (Eq, Ord, Functor)

infixr 3 :*:
data (f :*: g) a = f a :*: g a deriving (Eq, Ord, Functor)

infixr 4 :.:
newtype (f :.: g) a = CIRC (f (g a)) deriving (Eq, Ord, Functor)

newtype KF b a = KF b deriving (Eq, Ord, Functor)

type KRec a = KF a a
type KID a = KF () a

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