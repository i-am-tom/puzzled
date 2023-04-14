module Lambda where

import DTC

data DeBVarF a = DeBVarF Int deriving (Show, Eq, Ord, Functor)
data LamF a = LamF a deriving (Show, Eq, Ord, Functor)
data ApplF a = ApplF a a deriving (Show, Eq, Ord, Functor)

var :: (DeBVarF :<: g) => Int -> Fix g
var x = inject $ DeBVarF x

lam :: (LamF :<: g) => Fix g -> Fix g
lam x = inject $ LamF x

(<^>) :: (ApplF :<: g) => Fix g -> Fix g -> Fix g
(<^>) a b = inject $ ApplF a b

class Exchange f a where
    exchangeAlg :: a -> Algebra f (Int -> a)

exchange :: (Functor f, Exchange f (Fix f)) => Fix f -> Fix f -> Fix f
exchange = exchange' 0

exchange' :: (Functor f, Exchange f (Fix f)) => Int -> Fix f -> Fix f -> Fix f
exchange' n e x = foldF (exchangeAlg x) e $ n

instance (DeBVarF :<: f) => Exchange DeBVarF (Fix f) where
    exchangeAlg x _ (DeBVarF n') n
        | n' == n = x
        | otherwise = var n'

instance (LamF :<: f) => Exchange LamF (Fix f) where
    exchangeAlg _ r (LamF e) n = lam $ r e (n + 1)

instance (ApplF :<: f) => Exchange ApplF (Fix f) where
    exchangeAlg _ r (ApplF a b) n = (r a n) <^> (r b n)


instance (f :<: h, g :<: h) => Exchange (f :+: g) (Fix h) where
    exchangeAlg _ r (Inl f) n = inject $ fmap (flip r n) f
    exchangeAlg _ r (Inr g) n = inject $ fmap (flip r n) g


data EvalRes a = EvalRes {
    orig :: a,
    res :: a
}

class EvalStep f a where
    evalStepAlg :: Algebra f (EvalRes a)

evalStep :: (Functor f, EvalStep f (Fix f)) => Fix f -> Fix f
evalStep = res . foldF evalStepAlg

eval :: (Functor f, EvalStep f (Fix f), Eq (Fix f)) => Fix f -> Fix f
eval f 
    | f == f' = f'
    | otherwise = eval f'
    where f' = evalStep f

instance (DeBVarF :<: f) => EvalStep DeBVarF (Fix f) where
    evalStepAlg _ (DeBVarF n) = EvalRes {
        orig = var n,
        res = var n
    }

instance (LamF :<: f) => EvalStep LamF (Fix f) where
    evalStepAlg r (LamF e) = EvalRes {
        orig = lam (orig $ r e),
        res = lam (orig $ r e)
    }

instance (ApplF :<: f, LamF :<: f, Exchange f (Fix f)) => EvalStep ApplF (Fix f) where
    evalStepAlg r (ApplF a b) = EvalRes {
        orig = (orig $ r a) <^> (orig $ r b),
        res = case res (r a) of
            In (proj -> Just (LamF e)) -> exchange' 1 e (orig $ r b)
            _ -> (orig $ r a) <^> (orig $ r b)
    }

