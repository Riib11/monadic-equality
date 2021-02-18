module Relation.Equality where

import Relation

{-
# Equality

An equality is encoded by
  - a witness GADT `e :: * -> *`
  - an equality measure `eq :: a -> a -> e a -> Bool`
  - a domain type `a :: *`
  - proofs that the relation specified by `e`, eq`, `a` is an equivalence
    relation i.e. is
      - reflexive (`IsReflexive`)
      - symmetric (`IsSymmetric`)
      - transitive (`IsTransitive`)
      - substitutive (`IsSubstitutive`)
-}

{-@
data IsEquality e a b <eq :: a -> a -> e a -> Bool, eqb :: b -> b -> e b -> Bool> = IsEquality
  { isReflexive :: IsReflexive <eq> e a,
    isSymmetric :: IsSymmetric <eq> e a,
    isTransitive :: IsTransitive <eq> e a,
    isSubstitutive :: IsEquality <eqb, eqb> e b b -> IsSubstitutive <eq, eqb> e a b
  }
@-}
data IsEquality e a b
  = IsEquality
      (IsReflexive e a)
      (IsSymmetric e a)
      (IsTransitive e a)
      (IsEquality e b b -> IsSubstitutive e a b)

isReflexive :: IsEquality e a b -> IsReflexive e a
isReflexive (IsEquality isReflexive_ _ _ _) = isReflexive_

isSymmetric :: IsEquality e a b -> IsSymmetric e a
isSymmetric (IsEquality _ isSymmetric_ _ _) = isSymmetric_

isTransitive :: IsEquality e a b -> IsTransitive e a
isTransitive (IsEquality _ _ isTransitive_ _) = isTransitive_

isSubstitutive :: forall e a b. IsEquality e a b -> IsEquality e b b -> IsSubstitutive e a b
isSubstitutive (IsEquality _ _ _ isSubstitutive_) = isSubstitutive_
