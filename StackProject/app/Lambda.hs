module Lambda where

import DTC

data DeBVarF a = DeBVarF Int deriving (Show, Eq, Ord, Functor)
data LamF a = LamF a deriving (Show, Eq, Ord, Functor)
data ApplF a = ApplF a a deriving (Show, Eq, Ord, Functor)

var :: (DeBVarF :<: g) => Int -> g a
var x = inj $ DeBVarF x

lam :: (LamF :<: g) => a -> g a
lam x = inj $ LamF x

(<^>) :: (ApplF :<: g) => a -> a -> g a
(<^>) a b = inj $ ApplF a b

class Exchange f a where
    exchangeAlg :: a -> Algebra f (Int -> a)

exchange :: (Functor f, Exchange f (Fix f)) => Fix f -> Fix f -> Fix f
exchange = exchange' 0

exchange' :: (Functor f, Exchange f (Fix f)) => Int -> Fix f -> Fix f -> Fix f
exchange' n e x = foldF (exchangeAlg x) e $ n

instance (DeBVarF :<: f) => Exchange DeBVarF (Fix f) where
    exchangeAlg x _ (DeBVarF n') n
        | n' == n = x
        | otherwise = In $ var n'

instance (LamF :<: f) => Exchange LamF (Fix f) where
    exchangeAlg x r (LamF e) n = r e (n + 1)

instance (ApplF :<: f) => Exchange ApplF (Fix f) where
    exchangeAlg x r (ApplF a b) n = In $ (r a n) <^> (r b n)


instance (f :<: h, g :<: h) => Exchange (f :+: g) (Fix h) where
    exchangeAlg x r (Inl f) n = In $ inj $ fmap (flip r n) f
    exchangeAlg x r (Inr g) n = In $ inj $ fmap (flip r n) g


class EvalStep f a where
    evalStepAlg :: Algebra f a

instance (DeBVarF :<: f) => EvalStep DeBVarF (Fix f) where
    evalStepAlg _ (DeBVarF n) = In $ var n

instance (LamF :<: f) => EvalStep LamF (Fix f) where
    evalStepAlg r l = In $ inj $ fmap r l --TODO: recursive call should not be used! Id is returned!

instance (ApplF :<: f) => EvalStep ApplF (Fix f) where
    evalStepAlg r (ApplF a b) = _ --TODO: Maybe we need touple of evaluated an nonevaluated value. Problem: May read a value without changing it