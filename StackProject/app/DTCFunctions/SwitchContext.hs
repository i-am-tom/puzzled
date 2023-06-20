module DTCFunctions.SwitchContext where

import DTC
import Control.Monad

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
