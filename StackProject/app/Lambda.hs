module Lambda where

import DTC

data LambdaF a = Var Int | Lam a | a :<^>: a deriving (Show, Eq, Ord, Functor)

var :: (LambdaF :<: g) => Int -> g a
var x = inj $ Var x

lam :: (LambdaF :<: g) => a -> g a
lam x = inj $ Lam x

(<^>) :: (LambdaF :<: g) => a -> a -> g a
(<^>) a b = inj $ a :<^>: b

class (f :<: g) => Exchange f g where
    exchangeAlg :: Fix g -> Algebra f (Int -> Fix g)

exchange :: (Exchange f g) => Fix g -> Fix f -> Fix g
exchange = exchange' 0

exchange' :: (Exchange f g) => Int -> Fix g -> Fix f -> Fix g
exchange' n x e = foldF (exchangeAlg x) e $ n

instance (LambdaF :<: g) => Exchange LambdaF g where
    exchangeAlg x _ (Var n') n
        | n == n' = x
        | otherwise = In $ var n'
    exchangeAlg _ r (Lam e) n = In $ lam $ (r e) (n + 1)
    exchangeAlg _ r (e1 :<^>: e2) n = In $ (r e1 $ n) <^> (r e2 $ n)

--TODO: Problem: Exchange has to be pushed into higher functor
instance forall f g h. (Exchange f h, Exchange g h, ((f :+: g) :<: h)) => Exchange (f :+: g) h where
    exchangeAlg x r (Inl f) n = In $ inj $ fmap (flip r n) f
    exchangeAlg x r (Inr g) n = In $ inj $ fmap (flip r n) g


class EvalStep f where
    evalStepAlg :: f a -> a


