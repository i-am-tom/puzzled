{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module VarMonads where

class NCVarMonad c v m | v -> c where
    new :: (c a) => a -> m (v a)
    read :: v a -> m a
    write :: v a -> a -> m ()

data TFunc a b = TFunc {
    to :: a -> Maybe b,
    from :: b -> a
}

data TCPointer c v a = forall b. (c b) => TPointer{
    orig :: v b,
    tfunc :: TFunc b a 
}

data HOAS_FNCDVarMonad arr c v r where
    NewFNCD :: (c a) => a -> HOAS_FNCDVarMonad arr c v (v a)
    ReadFNCD :: v a -> HOAS_FNCDVarMonad arr c v a
    WriteFNCD :: v a -> a -> HOAS_FNCDVarMonad arr c v ()
    ReturnFNCD :: a -> HOAS_FNCDVarMonad arr c v a
    BindFNCD :: 
        HOAS_FNCDVarMonad arr c v a -> 
        (arr a (HOAS_FNCDVarMonad arr c v b)) -> 
        HOAS_FNCDVarMonad arr c v b

class SpecValVar v b where
    valPtr :: v a -> v b

data CHOAS c r where
    CHOAS_Val :: (c a) => a -> CHOAS c a
    CHOAS_Appl :: CHOAS c (a -> b) -> CHOAS c a -> CHOAS c b
    CHOAS_Lam :: (CHOAS c a -> CHOAS c b) -> CHOAS c (a -> b)

class (c a, d a) => C_AND c d a
instance (c a, d a) => C_AND c d a
class (forall a. C_AND c d a) => CDeriv c d
instance (forall a. C_AND c d a) => CDeriv c d

deriving instance CDeriv c Eq => Eq (CHOAS c r) 