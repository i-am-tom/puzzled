{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module VarMonads where

import Data.Typeable
import Data.Maybe
import Control.Monad.State.Strict

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
            --TODO: Here, the type itself should contain the possibility
            --to be a lambda calculus function. Problem: In this case, we 
            --loose the type safety when making this composable.
            --possible solution: use some HOAS as arrow type
        arr (a -> (HOAS_FNCDVarMonad arr c v b)) -> 
        HOAS_FNCDVarMonad arr c v b

class SpecValVar v b where
    valPtr :: v a -> v b

data CHOAS c r where
    CHOAS_Var :: Int -> CHOAS c a    
    CHOAS_Val :: (c a, Typeable a) => a -> CHOAS c a
    CHOAS_Appl :: (Typeable c, Typeable a, Typeable b) => CHOAS c (a -> b) -> CHOAS c a -> CHOAS c b
    CHOAS_Lam :: (Typeable a, c a) => (CHOAS c a -> CHOAS c b) -> CHOAS c (a -> b)

choasVal :: CHOAS c a -> a
choasVal (CHOAS_Var _) = error "cannot get value from variable placeholder"
choasVal (CHOAS_Val x) = x
choasVal (CHOAS_Appl ab a) = (choasVal ab) (choasVal a)
choasVal (CHOAS_Lam f) = choasVal . f . CHOAS_Val

class (c a, d a) => C_AND c d a
instance (c a, d a) => C_AND c d a
class (forall a. C_AND c d a) => CDeriv c d
instance (forall a. C_AND c d a) => CDeriv c d

nextIndex :: State Int Int
nextIndex = state $ \x -> (x , x + 1)

alphaEq :: (CDeriv c Eq) => (CHOAS c r) -> (CHOAS c r) -> State Int Bool
alphaEq (CHOAS_Var x) (CHOAS_Var y) = return $ x == y
alphaEq (CHOAS_Val x) (CHOAS_Val y) = return $ x == y
alphaEq (CHOAS_Appl ab a) (CHOAS_Appl ab' a') = 
    if typeOf a /= typeOf a' 
    then return False 
    else 
        (&&) <$>
        (alphaEq (fromJust $ cast ab) ab') <*>
        (alphaEq (fromJust $ cast a) a')
alphaEq (CHOAS_Lam f) (CHOAS_Lam f') = do
    n <- nextIndex
    alphaEq (f (CHOAS_Var n)) (f' (CHOAS_Var n))
alphaEq _ _ = return False

instance (Typeable r, CDeriv c Eq) => Eq (CHOAS c r) where
    x == y = evalState (alphaEq x y) 0