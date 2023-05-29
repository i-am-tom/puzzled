{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Propagator.ExecuteTest where

import Control.Arrow (runKleisli)
import Control.Category.Hierarchy
import Control.Category.Propagate (Propagate (unify))
import Control.Category.Reify (Reify (..))
import Control.Monad.Primitive (PrimMonad)
import Data.Functor ((<&>))
import Data.Kind (Constraint, Type)
import Data.Monoid.JoinSemilattice (JoinSemilattice)
import Data.Primitive.MutVar (newMutVar, readMutVar)
import Data.Set (Set)
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Propagator.Execute
import Test.Hspec (Spec, it, shouldBe)
import Prelude hiding (const, curry, id, uncurry, (.))

spec_execute :: Spec
spec_execute = do
  it "x = 5; x = ?" do
    let go :: Execute IO Unit (Set Char)
        go = const ['a']

    runKleisli (execute go) Terminal >>= \(Object ref) ->
      with ref \x -> x `shouldBe` ['a']

  it "x = 5; x = y; y = ?" do
    let go :: Execute IO Unit (Set Char)
        go = exr . (unify &&& exr) . (const ['a'] &&& const mempty)
    -- \^ exr . (unify &&& exr) means we explicitly check the unknown
    -- variable.

    runKleisli (execute go) Terminal >>= \(Object ref) ->
      with ref \x -> x `shouldBe` ['a']

  it "x = 5; x = y; y = z; z = ?" do
    let go :: Execute IO Unit (Set Char)
        go = unify . ((unify . exl) &&& exr) . (const ['a'] &&& const mempty &&& const mempty)
    -- \^ Assuming the above test worked, we don't do the same dance as
    -- above.

    runKleisli (execute go) Terminal >>= \(Object ref) ->
      with ref \x -> x `shouldBe` ['a']

  it "{ 1 } ⊂ x; { 2 } ⊂ y; { 3 } ⊂ z; x = y; y = z; x = ?" do
    let go :: Execute IO Unit (Set Int)
        go = unify . ((unify . exl) &&& exr) . (const [1] &&& const [2] &&& const [3])

    runKleisli (execute go) Terminal >>= \(Object ref) ->
      with ref \x -> x `shouldBe` [1, 2, 3]

---

genSet :: Gen (Set Char)
genSet = Gen.set (Range.linear 0 10) Gen.alphaNum

type Testable :: Type -> Constraint
type Testable = JoinSemilattice && Eq && Show

-- | The easiest way to check for equality is to run both programs with the
-- same input, and compare the outputs.
(=~=) ::
  (PrimMonad m) =>
  Reify Testable (Set Char) (Set Char) ->
  Reify Testable (Set Char) (Set Char) ->
  PropertyT m ()
fs =~= gs = do
  x <- forAll genSet

  let Execute f = interpret fs
      Execute g = interpret gs

  this <- newMutVar (x, pure ()) >>= f . Object . Value >>= \(Object y) -> fst <$> readMutVar (ref y)
  that <- newMutVar (x, pure ()) >>= g . Object . Value >>= \(Object y) -> fst <$> readMutVar (ref y)

  this === that

infix 5 =~=

interpret :: (MonadFail m, PrimMonad m) => Reify Testable i o -> Execute m i o
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
  Unify -> unify

genProgram :: Gen (Reify Testable (Set Char) (Set Char))
genProgram =
  Gen.recursive
    Gen.choice
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
