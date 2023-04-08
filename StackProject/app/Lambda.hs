module Lambda where

import DTC

data LambdaF a = Var Int | Lam a | a :<^>: a deriving (Show, Eq, Ord, Functor)

var :: (LambdaF :<: g) => Int -> g a
var x = inj $ Var x

lam :: (LambdaF :<: g) => a -> g a
lam x = inj $ Lam x

(<^>) :: (LambdaF :<: g) => a -> a -> g a
(<^>) a b = inj $ a :<^>: b

class (Functor f) => Exchange f where
    exchangeAlg :: Fix f -> Algebra f (Int -> Fix f)

exchange :: (Exchange f) => Fix f -> Fix f -> Fix f
exchange = exchange' 0

exchange' :: (Exchange f) => Int -> Fix f -> Fix f -> Fix f
exchange' n e x = foldF (exchangeAlg x) e $ n

instance (Functor f, LambdaF :<: f) => Exchange f where
    exchangeAlg x _ (proj -> Just (Var n')) n
        | n == n' = x
        | otherwise = In $ var n'
    exchangeAlg _ r (proj -> Just (Lam e)) n = In $ lam $ (r e) (n + 1)
    exchangeAlg _ r (proj -> Just (e1 :<^>: e2)) n = In $ (r e1 $ n) <^> (r e2 $ n)
    exchangeAlg _ r e n = In $ fmap (flip r n) e --TODO: Probably not the intended behaviour

{-}
instance Exchange (f :+: g) where
    exchangeAlg x r (Inl f) n = In $ inj $ fmap (flip r n) f
    exchangeAlg x r (Inr g) n = In $ inj $ fmap (flip r n) g
    -}

{-}
class EvalStep f g where
    evalStepAlg :: Algebra f (Fix g)

instance (Exchange LambdaF g) => EvalStep LambdaF g where
    evalStepAlg r ((r -> In (proj -> (Just (Lam (proj -> Just e))))) :<^>: x) = exchange (In e) x
    evalStepAlg r (e1 :<^>: e2) = undefined
    evalStepAlg r e = In $ inj $ (fmap r e)
        -}
