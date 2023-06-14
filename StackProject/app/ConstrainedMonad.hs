{-# LANGUAGE NoImplicitPrelude, RebindableSyntax #-}
module ConstrainedMonad where

import Prelude hiding (return, (>>=), (>>))
import Data.Kind

class CMonad c m | m -> c where
    return :: (c a) => a -> m a
    (>>=) :: (c a) => m a -> (a -> m b) -> m b

class Determine (m :: Type -> Type) (c :: Type -> Constraint) | m -> c

--instance (Monad m, Determine m c) => CMonad c m where
--    return = return
--    (>>=) = (>>=)

--f :: (CMonad c m, forall x. c x => Eq x) => ... QuantifiedConstraints

test :: (CMonad c m, c Int) => m Int
test = do 
    x <- return 3
    return (x + 4)

data FCMonad c r where
    FReturn :: c a => a -> FCMonad c a
    (:>>=:) :: c a => FCMonad c a -> (a -> FCMonad c b) -> FCMonad c b

instance c ~ d => CMonad c (FCMonad d) where
    return = FReturn
    (>>=)  = (:>>=:)

f :: FCMonad Show Int
f = return 3

{-
printList :: [a] -> m ()
printList [] = return ()
printList (x :: xs) = print x >> printList xs
-}