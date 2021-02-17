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
data IsEquality e a <eq :: forall a. a -> a -> e a -> Bool> = IsEquality
  { isReflexive :: IsReflexive <eq> e a,
    isSymmetric :: IsSymmetric <eq> e a,
    isTransitive :: IsTransitive <eq> e a
  }
@-}
data IsEquality e a
  = IsEquality
      (IsReflexive e a)
      (IsSymmetric e a)
      (IsTransitive e a)

-- isSubstitutive :: forall b. IsEquality <eq> e b -> IsSubstitutive <eq> e a b
-- (forall b. IsEquality e b -> IsSubstitutive e a b)

{-@
isReflexive ::
  forall <eq :: a -> a -> e a -> Bool>.
  IsEquality <eq> e a -> IsReflexive <eq> e a
@-}
isReflexive :: IsEquality e a -> IsReflexive e a
isReflexive (IsEquality isReflexive_ _ _) = isReflexive_

{-@
isSymmetric ::
  forall <eq :: a -> a -> e a -> Bool>.
  IsEquality <eq> e a -> IsSymmetric <eq> e a
@-}
isSymmetric :: IsEquality e a -> IsSymmetric e a
isSymmetric (IsEquality _ isSymmetric_ _) = isSymmetric_

{-@
isTransitive ::
  forall <eq :: a -> a -> e a -> Bool>.
  IsEquality <eq> e a -> IsTransitive <eq> e a
@-}
isTransitive :: IsEquality e a -> IsTransitive e a
isTransitive (IsEquality _ _ isTransitive_) = isTransitive_

-- {-@
-- isSubstitutive ::
--   forall <eq :: forall a. a -> a -> e a -> Bool>.
--   IsEquality <eq> e a -> forall b. IsEquality <eq> e b -> IsSubstitutive <eq> e a b
-- @-}
-- isSubstitutive :: IsEquality e a -> forall b. IsEquality e b -> IsSubstitutive e a b
-- isSubstitutive (IsEquality _ _ _ isSubstitutive_) = isSubstitutive_
