module Relation.Equality where

import Relation

{-
# Equality

An equality is encoded by
  - a witness GADT `e :: * -> *`
  - an equality measure `eq :: a -> a -> e a -> Bool` (and a copy `eqb`, since abstract predicates are not polymorphic)
  - a domain type `a :: *`
  - proofs that the relation specified by `e`, eq`, `a` is an equivalence
    relation i.e. is
      - reflexive (`IsReflexive`)
      - symmetric (`IsSymmetric`)
      - transitive (`IsTransitive`)
      - substitutive (`IsSubstitutive`)
-}

{-@
data IsEquality e a <eq :: a -> a -> e a -> Bool> = IsEquality
@-}
data IsEquality (e :: * -> *) a = IsEquality

-- {-@
-- constructIsEquality ::
