module Relation.Equality where

import Relation

{-
# Equality

An equality relation is a relation that is reflexive, symmetric, and transitive.
-}

{-@
data IsEquality eq a = IsEquality
  { equ_isRelation :: IsRelation eq a,
    equ_isReflexive :: IsReflexive eq a,
    equ_isSymmetric :: IsSymmetric eq a,
    equ_isTransitive :: IsTransitive eq a
  }
@-}
data IsEquality eq a = IsEquality
  { equ_isRelation :: IsRelation eq a,
    equ_isReflexive :: IsReflexive eq a,
    equ_isSymmetric :: IsSymmetric eq a,
    equ_isTransitive :: IsTransitive eq a
  }
