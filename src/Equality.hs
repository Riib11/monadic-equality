module Equality where

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
-}

{-@
data IsEquality e a <eq :: a -> a -> e a -> Bool> = IsEquality
  { isReflexive :: IsReflexive e a <eq>,
    isSymmetric :: IsSymmetric e a <eq>,
    isTransitive :: IsTransitive e a <eq>
  }
@-}
data IsEquality e a
  = IsEquality
      (IsReflexive e a)
      (IsSymmetric e a)
      (IsTransitive e a)

isReflexive :: IsEquality e a -> IsReflexive e a
isReflexive (IsEquality isReflexive_ _ _) = isReflexive_

isSymmetric :: IsEquality e a -> IsSymmetric e a
isSymmetric (IsEquality _ isSymmetric_ _) = isSymmetric_

isTransitive :: IsEquality e a -> IsTransitive e a
isTransitive (IsEquality _ _ isTransitive_) = isTransitive_
