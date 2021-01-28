module Equality where

import Relation

{-
# Equality

An equality relation is a relation that is reflexive, symmetric, and transitive.
-}

data IsEquality eq a = IsEquality
  { isRelation :: IsRelation eq a,
    isReflexive :: IsReflexive eq a,
    isSymmetric :: IsSymmetric eq a,
    isTransitive :: IsTransitive eq a
  }

{-
# SMT Equality

A proxy for Haskell's `Eq` class, used by Liquid Haskell's SMT solver to
represent equalities.
-}

data SMTEquality a = SMTEquality
  {eq_smt :: a -> a -> Bool}

{-@ assume isRelation_SMTEquality_Int :: IsRelation SMTEquality Int @-}
isRelation_SMTEquality_Int :: IsRelation SMTEquality Int
isRelation_SMTEquality_Int = undefined

{-@ assume isReflexive_SMTEquality_Int :: IsReflexive SMTEquality Int @-}
isReflexive_SMTEquality_Int :: IsReflexive SMTEquality Int
isReflexive_SMTEquality_Int = undefined

{-@ assume isSymmetric_SMTEquality_Int :: IsSymmetric SMTEquality Int @-}
isSymmetric_SMTEquality_Int :: IsSymmetric SMTEquality Int
isSymmetric_SMTEquality_Int = undefined

{-@ assume isTransitive_SMTEquality_Int :: IsTransitive SMTEquality Int @-}
isTransitive_SMTEquality_Int :: IsTransitive SMTEquality Int
isTransitive_SMTEquality_Int = undefined
