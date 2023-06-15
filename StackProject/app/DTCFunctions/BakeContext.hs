module DTCFunctions.BakeContext where

import DTC
import Control.Monad

{-}
class BakeContext f m v where
    bakeContextAlg :: (forall a. v a -> m a) -> Algebra (f :.: v) (m (Fix f))

instance (Functor f) => BakeContext f m v where
    bakeContextAlg read r (CIRC f) = fmap (read >=> r) f
    -}
{-}
foldContexts ::
    (Monad m) =>
    (forall a. v a -> m a) ->
    (Algebra f (m a)) ->
    Fix (f :.: v) -> m a
foldContexts read alg = foldF $ \r f' -> case f' of
    (CIRC f) -> alg (read >=> r) f
    -}