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
    exchangeAlg _ r (LamF e) n = In $ lam $ r e (n + 1)

instance (ApplF :<: f) => Exchange ApplF (Fix f) where
    exchangeAlg _ r (ApplF a b) n = In $ (r a n) <^> (r b n)


instance (f :<: h, g :<: h) => Exchange (f :+: g) (Fix h) where
    exchangeAlg _ r (Inl f) n = In $ inj $ fmap (flip r n) f
    exchangeAlg _ r (Inr g) n = In $ inj $ fmap (flip r n) g


data EvalRes a = EvalRes {
    orig :: a,
    res :: a
}

class EvalStep f a where
    evalStepAlg :: Algebra f (EvalRes a)

evalStep :: (Functor f, EvalStep f (Fix f)) => Fix f -> Fix f
evalStep = res . foldF evalStepAlg

instance (DeBVarF :<: f) => EvalStep DeBVarF (Fix f) where
    evalStepAlg _ (DeBVarF n) = EvalRes {
        orig = In $ var n,
        res = In $ var n
    }

instance (LamF :<: f) => EvalStep LamF (Fix f) where
    evalStepAlg r (LamF e) = EvalRes {
        orig = In $ lam (orig $ r e),
        res = In $ lam (orig $ r e)
    }

instance (ApplF :<: f, LamF :<: f, Exchange f (Fix f)) => EvalStep ApplF (Fix f) where
    evalStepAlg r (ApplF a b) = EvalRes {
        orig = In $ (orig $ r a) <^> (orig $ r b),
        res = case res (r a) of
            In (proj -> Just (LamF e)) -> exchange' 1 e (orig $ r b)
            _ -> In $ (orig $ r a) <^> (orig $ r b)
    }