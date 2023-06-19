module Lambda where

import DTC
import Text.Show.Combinators
import Data.Kind

data DeBVarF a = DeBVarF Int deriving (Eq, Ord, Functor)
data LamF a = LamF a deriving (Eq, Ord, Functor)
data ApplF a = ApplF a a deriving (Eq, Ord, Functor)

instance (Show a) => Show (DeBVarF a) where
    showsPrec d (DeBVarF n) = (showCon "var" @| n) d

instance (Show a) => Show (LamF a) where
    showsPrec d (LamF e) = (showCon "lam" @| e) d

instance (Show a) => Show (ApplF a) where
    showsPrec d (ApplF a b) = showInfixl "<^>" 5 (`showsPrec` a) (`showsPrec` b) d

type LambdaF = DeBVarF :+: LamF :+: ApplF

var :: (DeBVarF :<: g) => Int -> Fix g
var x = inject $ DeBVarF x

lam :: (LamF :<: g) => Fix g -> Fix g
lam x = inject $ LamF x

infixl 5 <^>
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


instance (Exchange f (Fix h), Exchange g (Fix h)) => Exchange (f :+: g) (Fix h) where
    exchangeAlg x r (Inl f) n = exchangeAlg x r f n
    exchangeAlg x r (Inr g) n = exchangeAlg x r g n


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

instance (Functor f, ApplF :<: f, LamF :<: f, Exchange f (Fix f)) => EvalStep ApplF (Fix f) where
    evalStepAlg r (ApplF a b) = EvalRes {
        orig = (orig $ r a) <^> (orig $ r b),
        res = case res (r a) of
            In (proj -> Just (LamF e)) -> exchange' 1 e (orig $ r b)
            _ -> (orig $ r a) <^> (orig $ r b)
    }

instance (EvalStep f (Fix h), EvalStep g (Fix h)) => 
    EvalStep (f :+: g) (Fix h) where
    evalStepAlg r (Inl f) = evalStepAlg r f
    evalStepAlg r (Inr g) = evalStepAlg r g

instance (Functor g, Functor f, f :.: g :<: h) => 
    EvalStep (f :.: g) (Fix h) where
    evalStepAlg r (CIRC fg) = EvalRes {
        orig = In $ inj $ CIRC $ fmap (fmap (orig . r)) fg ,
        res = In $ inj $ CIRC $ fmap (fmap (res . r)) fg
    }

instance (Functor g, Functor f, f :*: g :<: h) =>
    EvalStep (f :*: g) (Fix h) where
    evalStepAlg r (fa :*: ga) = EvalRes {
        orig = In $ inj $ (fmap (orig . r) fa) :*: (fmap (orig . r) ga) ,
        res = In $ inj $ (fmap (res . r) fa) :*: (fmap (res . r) ga)
    }

instance (KF b :<: h) => EvalStep (KF b) (Fix h) where
    evalStepAlg r kf = EvalRes {
        orig = In $ inj $ fmap (orig . r) kf ,
        res = In $ inj $ fmap (res . r) kf
    }

{-
data LamR rep b where
    ApplR :: rep (a -> b) -> rep a -> LamR rep b
    LamR :: (rep a -> rep c) -> LamR rep (a -> c)
-}

{-
Approach below is a nice idea, but does not really make sense. The Idea is that we get
some knowldge from the terms in the recursive call to create e.g. a data type that
knows its subparts make up a well-typed lambda term or something. However, the whole
idea behind the DTC is that we know nothing about what came about in the recursive call.
Typesafety or the like for terms should therefore be done separately, e.g. by folding 
over the term and returning whether a property holds or not. This is, admittedly, a lot
easier to do with dependent types than it is with Haskell. 


data LamR rep r where
    LamR :: (rep a -> rep b) -> LamR rep (a -> b)

data FixR (f :: (Type -> Type) -> Type -> Type) b = InR (f (FixR f) b)

instance (Functor (f (FixR f))) => Functor (FixR f) where
    fmap f (InR l) = InR (fmap f l)

type AlgebraR (f :: (Type -> Type) -> Type -> Type) a = forall g. f (FixR g) a -> a

foldR :: AlgebraR f a -> (FixR f) a -> a 
foldR alg (InR f) = alg f
-}