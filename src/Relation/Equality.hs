module Relation.Equality where

import Relation

{-
# Equality

An equality relation is a relation that is reflexive, symmetric, and transitive.
-}

{-@
data IsEquality eq a = IsEquality
  { eq_isRelation :: IsRelation eq a,
    eq_isReflexive :: IsReflexive eq a,
    eq_isSymmetric :: IsSymmetric eq a,
    eq_isTransitive :: IsTransitive eq a
  }
@-}
data IsEquality eq a = IsEquality
  { eq_isRelation :: IsRelation eq a,
    eq_isReflexive :: IsReflexive eq a,
    eq_isSymmetric :: IsSymmetric eq a,
    eq_isTransitive :: IsTransitive eq a
  }
