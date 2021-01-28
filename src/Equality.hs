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
