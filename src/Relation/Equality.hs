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
data IsEquality e a <eq :: a -> a -> e a -> Bool> = IsEquality
@-}
data IsEquality (e :: * -> *) a = IsEquality

{-@
type Helper f b = forall <fq :: b -> b -> f b -> Bool>. () -> ()
@-}

{-@
assume constructIsEquality ::
  forall e a <eq :: a -> a -> e a -> Bool>.
  IsReflexive <eq> e a ->
  IsSymmetric <eq> e a ->
  IsTransitive <eq> e a ->
  (forall f b. Helper f b) ->
  IsEquality <eq> e a
@-}
constructIsEquality ::
  IsReflexive e a ->
  IsSymmetric e a ->
  IsTransitive e a ->
  (forall f b. () -> ()) ->
  IsEquality e a
constructIsEquality _ _ _ _ = undefined

-- {-@
-- assume constructIsEquality ::
--   forall e a <eq :: a -> a -> e a -> Bool>.
--   IsReflexive <eq> e a ->
--   IsSymmetric <eq> e a ->
--   IsTransitive <eq> e a ->
--   (forall f b <fq :: b -> b -> f b -> Bool>. IsEquality <fq> f b -> IsSubstitutive <eq, fq> e f a b) ->
--   IsEquality <eq> e a
-- @-}
-- constructIsEquality ::
--   IsReflexive e a ->
--   IsSymmetric e a ->
--   IsTransitive e a ->
--   (forall f b. IsEquality f b -> IsSubstitutive e f a b) ->
--   IsEquality e a
-- constructIsEquality _ _ _ _ = undefined
