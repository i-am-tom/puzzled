{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Data.Monoid.JoinSemilatticeTest where

import Control.Monad (when)
import Data.Monoid.JoinSemilattice (JoinSemilattice (..), Merge (..))
import Data.Semigroup (All (All), Any (Any), Max (Max), Min (Min))
import Data.Set (Set)
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

lawAssociativity :: (Eq x, Semigroup x, Show x) => Gen x -> Property
lawAssociativity gen = property do
  x <- forAll gen
  y <- forAll gen
  z <- forAll gen

  x <> (y <> z) === (x <> y) <> z

lawIdentity :: (Eq x, Monoid x, Show x) => Gen x -> Property
lawIdentity gen = property do
  forAll gen >>= \x -> x <> mempty === x
{-# ANN lawIdentity "HLint: Monoid law" #-}

lawCommutativity :: (Eq x, Semigroup x, Show x) => Gen x -> Property
lawCommutativity gen = property do
  x <- forAll gen
  y <- forAll gen

  x <> y === y <> x

lawIdempotence :: (Eq x, Semigroup x, Show x) => Gen x -> Property
lawIdempotence gen = property do
  x <- forAll gen
  x <> x === x

lawMerge :: (Eq x, JoinSemilattice x, Show x) => Gen x -> Property
lawMerge gen = property do
  x <- forAll gen
  y <- forAll gen

  case x <~ y of
    Changed z -> x /== z
    Unchanged z -> x === z

lawMergeAgreement :: (Eq x, JoinSemilattice x, Show x) => Gen x -> Property
lawMergeAgreement gen = property do
  x <- forAll gen
  y <- forAll gen

  case x <~ y of
    Changed z -> x <> y === z
    Unchanged _ -> x <> y === x

lawImpliesReflexivity :: (Eq x, JoinSemilattice x, Show x) => Gen x -> Property
lawImpliesReflexivity gen = property do
  x <- forAll gen
  y <- forAll gen

  if x `implies` y && y `implies` x
    then x === y
    else x /== y

lawImpliesTransitivity :: (JoinSemilattice x, Show x) => Gen x -> Property
lawImpliesTransitivity gen = property do
  x <- forAll gen
  y <- forAll gen
  z <- forAll gen

  when (x `implies` y && y `implies` z) do
    diff x implies z

---

hprop_any_commutativity :: Property
hprop_any_commutativity = lawCommutativity (fmap Any Gen.bool)

hprop_any_idempotence :: Property
hprop_any_idempotence = lawIdempotence (fmap Any Gen.bool)

hprop_any_merge :: Property
hprop_any_merge = lawMerge (fmap Any Gen.bool)

hprop_any_merge_agreement :: Property
hprop_any_merge_agreement = lawMergeAgreement (fmap Any Gen.bool)

hprop_any_implies_reflexivity :: Property
hprop_any_implies_reflexivity = lawImpliesReflexivity (fmap Any Gen.bool)

hprop_any_implies_transitivity :: Property
hprop_any_implies_transitivity = lawImpliesTransitivity (fmap Any Gen.bool)

---

hprop_all_commutativity :: Property
hprop_all_commutativity = lawCommutativity (fmap All Gen.bool)

hprop_all_idempotence :: Property
hprop_all_idempotence = lawIdempotence (fmap All Gen.bool)

hprop_all_merge :: Property
hprop_all_merge = lawMerge (fmap All Gen.bool)

hprop_all_merge_agreement :: Property
hprop_all_merge_agreement = lawMergeAgreement (fmap All Gen.bool)

hprop_all_implies_reflexivity :: Property
hprop_all_implies_reflexivity = lawImpliesReflexivity (fmap All Gen.bool)

hprop_all_implies_transitivity :: Property
hprop_all_implies_transitivity = lawImpliesTransitivity (fmap All Gen.bool)

---

hprop_max_commutativity :: Property
hprop_max_commutativity = lawCommutativity (fmap Max Gen.alphaNum)

hprop_max_idempotence :: Property
hprop_max_idempotence = lawIdempotence (fmap Max Gen.alphaNum)

hprop_max_merge :: Property
hprop_max_merge = lawMerge (fmap Max Gen.bool)

hprop_max_merge_agreement :: Property
hprop_max_merge_agreement = lawMergeAgreement (fmap Max Gen.bool)

hprop_max_implies_reflexivity :: Property
hprop_max_implies_reflexivity = lawImpliesReflexivity (fmap Max Gen.bool)

hprop_max_implies_transitivity :: Property
hprop_max_implies_transitivity = lawImpliesTransitivity (fmap Max Gen.bool)

---

hprop_min_commutativity :: Property
hprop_min_commutativity = lawCommutativity (fmap Min Gen.alphaNum)

hprop_min_idempotence :: Property
hprop_min_idempotence = lawIdempotence (fmap Min Gen.alphaNum)

hprop_min_merge :: Property
hprop_min_merge = lawMerge (fmap Min Gen.bool)

hprop_min_merge_agreement :: Property
hprop_min_merge_agreement = lawMergeAgreement (fmap Min Gen.bool)

hprop_min_implies_reflexivity :: Property
hprop_min_implies_reflexivity = lawImpliesReflexivity (fmap Min Gen.bool)

hprop_min_implies_transitivity :: Property
hprop_min_implies_transitivity = lawImpliesTransitivity (fmap Min Gen.bool)

---

genMerge :: Gen (Merge (Max Char))
genMerge = do
  result <- fmap Max Gen.alphaNum

  Gen.bool
    >>= pure . \case
      True -> Changed result
      False -> Unchanged result

hprop_merge_associativity :: Property
hprop_merge_associativity = lawAssociativity genMerge

hprop_merge_identity :: Property
hprop_merge_identity = lawIdentity genMerge

hprop_merge_commutativity :: Property
hprop_merge_commutativity = lawCommutativity genMerge

hprop_merge_idempotence :: Property
hprop_merge_idempotence = lawIdempotence genMerge

hprop_merge_merge :: Property
hprop_merge_merge = lawMerge genMerge

hprop_merge_merge_agreement :: Property
hprop_merge_merge_agreement = lawMergeAgreement genMerge

hprop_merge_implies_reflexivity :: Property
hprop_merge_implies_reflexivity = lawImpliesReflexivity genMerge

hprop_merge_implies_transitivity :: Property
hprop_merge_implies_transitivity = lawImpliesTransitivity genMerge

---

genSet :: Gen (Set Char)
genSet = Gen.set (Range.linear 0 100) Gen.alphaNum

hprop_set_associativity :: Property
hprop_set_associativity = lawAssociativity genSet

hprop_set_identity :: Property
hprop_set_identity = lawIdentity genSet

hprop_set_commutativity :: Property
hprop_set_commutativity = lawCommutativity genSet

hprop_set_idempotence :: Property
hprop_set_idempotence = lawIdempotence genSet

hprop_set_merge :: Property
hprop_set_merge = lawMerge genMerge

hprop_set_merge_agreement :: Property
hprop_set_merge_agreement = lawMergeAgreement genMerge

hprop_set_implies_reflexivity :: Property
hprop_set_implies_reflexivity = lawImpliesReflexivity genSet

hprop_set_implies_transitivity :: Property
hprop_set_implies_transitivity = lawImpliesTransitivity genSet
