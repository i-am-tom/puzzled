module DTC where

data Fix f = In (f (Fix f))

type Algebra f a = forall r. (r -> a) -> f r -> a

foldF :: (Functor f) => Algebra f a -> Fix f -> a
foldF alg (In f) = alg id $ fmap (foldF alg) f

class (Functor f, Functor g) => f :<: g where
    inj :: f a -> g a
    proj :: g a -> Maybe (f a)

data (f :+: g) a = Inl (f a) | Inr (g a)

instance (Functor f) => f :<: f where
    inj = id
    proj = Just

inject :: (f :<: g) => f (Fix g) -> Fix g
inject = In . inj