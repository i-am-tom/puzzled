module DTCFunctions.SwitchContext where

import DTC
import Control.Monad
import Data.Functor.Identity

{-}
class BakeContext f m v where
    bakeContextAlg :: (forall a. v a -> m a) -> Algebra (f :.: v) (m (Fix f))

instance (Functor f) => BakeContext f m v where
    bakeContextAlg read r (CIRC f) = fmap (read >=> r) f
    -}

class SwitchContext f m where
    switchContext :: f (m a) -> m (f a)

--TODO: Could some of these Instances be derived by the FunctorN classes?
instance {-# OVERLAPPING #-} (Functor m, SwitchContext f m, SwitchContext g m) => SwitchContext (f :+: g) m where
    switchContext (Inl f) = Inl <$> switchContext f
    switchContext (Inr g) = Inr <$> switchContext g

instance (Applicative m, SwitchContext f m, SwitchContext g m) => SwitchContext (f :*: g) m where
    switchContext (fa :*: ga) = (:*:) <$> switchContext fa <*> switchContext ga

instance (Functor m) => SwitchContext KRec m where
    switchContext (KRec m) = KRec <$> m

instance {-# OVERLAPPING #-}  (Applicative m, Functor0 f) => SwitchContext f m where
    switchContext _ = pure intro0

switchAlg :: forall m f a. (Functor m, Functor f, SwitchContext f m) => 
    Algebra f a -> Algebra f (m a)
switchAlg alg r f = fmap (alg id) $ switchContext $ fmap r f

switchAlgRead :: (Monad m, Functor f, SwitchContext f m) => 
    (forall a. v a -> m a) -> Algebra f a -> Algebra (f :.: v) (m a)
switchAlgRead read alg r (CIRC fv) = fmap (alg id) $ switchContext $ fmap (r <=< read) fv

class ContextFold f g m where
    foldC :: Algebra f a -> Fix g -> m a

instance (Functor f) => ContextFold f f Identity where
    foldC alg = foldF (\r -> Identity . alg (runIdentity . r))