{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}

module Propagator.ExecuteTest where

import Control.Category.Hierarchy
import Control.Category.Reify (Reify (..))
import Control.Monad.Primitive (PrimMonad)
import Data.Functor ((<&>))
import Data.Primitive.MutVar (newMutVar, readMutVar)
import Data.Set (Set)
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude hiding ((.), const, curry, id, uncurry)
import Propagator.Execute

genSet :: Gen (Set Char)
genSet = Gen.set (Range.linear 0 10) Gen.alphaNum

-- | The easiest way to check for equality is to run both programs with the
-- same input, and compare the outputs.
(=~=) :: PrimMonad m => Reify Show (Set Char) (Set Char) -> Reify Show (Set Char) (Set Char) -> PropertyT m ()
fs =~= gs = do
  x <- forAll genSet

  let Execute f = interpret fs
      Execute g = interpret gs

  this <- newMutVar x >>= f . Object . Value >>= \(Object y) -> readMutVar (ref y)
  that <- newMutVar x >>= g . Object . Value >>= \(Object y) -> readMutVar (ref y)

  this === that

infix 5 =~=

interpret :: PrimMonad m => Reify c i o -> Execute m i o
interpret = \case
  Compose f g -> interpret f . interpret g
  Identity -> id
  Fork f g -> interpret f &&& interpret g
  Exl -> exl
  Exr -> exr
  Curry f -> curry (interpret f)
  Uncurry f -> uncurry (interpret f)
  Kill -> kill
  Const x -> const x
  Unify -> error "TODO" -- unify

genProgram :: Gen (Reify Show (Set Char) (Set Char))
genProgram = Gen.recursive Gen.choice
  [ pure id,
    genSet <&> \x -> const x . kill
  ]
  [ Gen.subterm2 genProgram genProgram (.),

    Gen.subterm2 genProgram genProgram \x y -> exl . (x &&& y),
    Gen.subterm2 genProgram genProgram \x y -> exr . (x &&& y)
  ]

hprop_execute_right_identity :: Property
hprop_execute_right_identity = property do
  f <- forAll genProgram
  f . id =~= f

hprop_execute_left_identity :: Property
hprop_execute_left_identity = property do
  f <- forAll genProgram
  id . f =~= f

hprop_execute_associativity :: Property
hprop_execute_associativity = property do
  f <- forAll genProgram
  g <- forAll genProgram
  h <- forAll genProgram

  (f . (g . h)) =~= ((f . g) . h)

hprop_execute_cartesian :: Property
hprop_execute_cartesian = property do
  f <- forAll genProgram
  g <- forAll genProgram

  exl . (f &&& g) =~= f
  exr . (f &&& g) =~= g
