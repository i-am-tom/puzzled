{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Propagator.ExecuteTest where

import Control.Applicative (Alternative (empty))
import Control.Category.Hierarchy
import Control.Category.Propagate (Propagate (choice, unify))
import Control.Category.Reify (Reify (..), Void)
import Control.Monad.Branch (BranchT, all)
import Control.Monad.Primitive (PrimMonad (PrimState), RealWorld)
import Data.Boring (absurd)
import Data.Constraint.Extra (type (&&))
import Data.Kind (Constraint, Type)
import Data.Monoid.JoinSemilattice (JoinSemilattice)
import Data.Set (Set)
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Propagator.Cell (unsafeRead)
import Propagator.Execute
import Test.Hspec (Spec, it, shouldBe)
import Type.Reflection (Typeable)
import Prelude hiding (all, const, curry, id, uncurry, (.))

type Tester :: Type -> Type
type Tester = Execute (BranchT IO) Unit

spec_execute :: Spec
spec_execute = do
  it "x = 'a'; x = ?" do
    let go :: Tester (Set Char)
        go = const ['a']

    run go >>= \output -> output `shouldBe` [['a']]

  it "x = 'a'; x = y; y = ?" do
    let go :: Tester (Set Char)
        go = exr . (unify &&& exr) . (const ['a'] &&& const mempty)
    -- \^ exr . (unify &&& exr) means we explicitly check the unknown
    -- variable.

    run go >>= \output -> output `shouldBe` [['a']]

  it "x ⊂ 'a'; x = y; y = z; z ⊂ ?" do
    let go :: Tester (Set Char)
        go = unify . ((unify . exl) &&& exr) . (const ['a'] &&& const mempty &&& const mempty)
    -- \^ Assuming the above test worked, we don't do the same dance as
    -- above.

    run go >>= \output -> output `shouldBe` [['a']]

  it "{ 1 } ⊂ x; { 2 } ⊂ y; { 3 } ⊂ z; x = y; y = z; ? ⊂ x" do
    let go :: Tester (Set Int)
        go = unify . ((unify . exl) &&& exr) . (const [1] &&& const [2] &&& const [3])

    run go >>= \output -> output `shouldBe` [[1, 2, 3]]

  it "x ⊂ { 1, 2 }; x = y; y = ?" do
    let go :: Tester (Set Int)
        go = choice . (const [1] &&& const [2])

    run go >>= \output -> output `shouldBe` [[1], [2]]

run :: (PrimMonad m, PrimState m ~ RealWorld) => Execute (BranchT m) Unit o -> m [o]
run k = all $ execute k Terminal >>= \case Object ref -> unsafeRead ref; _ -> empty

---

genSet :: Gen (Set Char)
genSet = Gen.set (Range.linear 0 10) Gen.alphaNum

type Testable :: Type -> Constraint
type Testable = JoinSemilattice && Eq && Show

-- | The easiest way to check for equality is to run both programs with the
-- same input, and compare the outputs.
(=~=) ::
  (PrimMonad m, PrimState m ~ RealWorld) =>
  Reify Testable Void (Set Char) (Set Char) ->
  Reify Testable Void (Set Char) (Set Char) ->
  PropertyT m ()
fs =~= gs = do
  x <- forAll genSet

  this <- all (forwards (interpret fs) x)
  that <- all (forwards (interpret gs) x)

  this === that

infix 5 =~=

interpret :: (MonadFail m, PrimMonad m, Typeable i, Typeable o) => Reify Testable Void i o -> Execute (BranchT m) i o
interpret = \case
  Compose f g -> interpret f . interpret g
  Identity -> id
  Fork f g -> interpret f &&& interpret g
  Exl -> exl
  Exr -> exr
  Curry f -> curry (interpret f)
  Uncurry f -> uncurry (interpret f)
  Kill -> kill
  Const x -> const_ x
  Choice -> choice
  Unify -> unify
  Other v -> absurd v

genProgram :: Gen (Reify Testable Void (Set Char) (Set Char))
genProgram =
  Gen.recursive
    Gen.choice
    [ pure id,
      fmap const_ genSet
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
