module LambdaVarMonad where

import Lambda hiding (var, lam, (<^>))
import DTC
import NewConstrDefVarMonad (NewConstrDefVarMonad, new')

circInject :: (f :<: g) => f (v (Fix (g :.: v))) -> Fix (g :.: v)
circInject = In . CIRC . inj

var :: forall g v . (DeBVarF :<: g) => Int -> Fix (g :.: v)
var x = circInject $ DeBVarF x

lam :: forall g v . (LamF :<: g) => v (Fix (g :.: v)) -> Fix (g :.: v)
lam x = circInject $ LamF x

infixl 5 <^>
(<^>) :: forall g v . (ApplF :<: g) => v (Fix (g :.: v)) -> v (Fix (g :.: v)) -> Fix (g :.: v)
(<^>) a b = circInject $ ApplF a b

var' :: forall g c m v . (
      Monad m
    , NewConstrDefVarMonad c m v
    , c (Fix (g :.: v))
    , DeBVarF :<: g) => 
    Int -> m (v (Fix (g :.: v)))
var' = new' . var

lam' :: forall g c m v . (
      Monad m
    , NewConstrDefVarMonad c m v
    , c (Fix (g :.: v))
    , LamF :<: g) =>
    m (v (Fix (g :.: v))) -> m (v (Fix (g :.: v)))
lam' m = new' =<< (lam <$> m)

infixl 5 <^>*
(<^>*) :: forall g c m v . (
      Monad m
    , NewConstrDefVarMonad c m v
    , c (Fix (g :.: v))
    , ApplF :<: g) =>
    m (v (Fix (g :.: v))) -> m (v (Fix (g :.: v))) -> m (v (Fix (g :.: v)))
(<^>*) a b = new' =<< ((<^>) <$> a <*> b)

{-}
bake :: forall g c m v . (
      Monad m
    , NewConstrDefVarMonad c m v) =>
    Fix ()
    -}