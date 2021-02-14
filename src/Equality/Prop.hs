module Equality.Prop where

import qualified Equality
import qualified Equality.SMT
import ProofCombinators
import qualified Relation

-- TODO: build with liquidhaskell develop branch

{-
# Propositional Equality
-}

-- Measure. Uninterpreted measure for propositional equality.
{-@
measure eqprop :: x:a -> y:a -> EqualProp a -> Bool
@-}

-- Type Synonym. Witness to `a`-equality between `X` and `Y`.
{-@
type EqProp a X Y = (EqualProp a)<eqprop X Y>
@-}

-- Inductive Datatype.
{-@
data EqualProp :: * -> * where
    InjectSMT ::
      x:a -> y:a ->
      Equality.SMT.EqSMT a {x} {y} ->
      EqProp a {x} {y}
  | Extensionality ::
      f:(a -> b) -> g:(a -> b) ->
      (x:a -> EqProp a {f x} {g x}) ->
      EqProp a {f} {g}
  | Congruency ::
      x:a -> y:a -> c:(a -> b) ->
      EqProp a {x} {y} ->
      EqProp b {f x} {f y}
@-}
data EqualProp :: * -> * where
  InjectSMT :: a -> a -> EqualSMT a -> EqualProp a
  Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualProp a) -> EqualProp a
  Congruency :: a -> a -> (a -> b) -> EqualProp a -> EqualProp b

{-
## Properties
-}

{-@
type IsReflexive a = Relation.IsReflexive <{\x y w -> eqprop x y w}> EqualProp a
@-}
type IsReflexive a = Relation.IsReflexive EqualProp a

{-@
type IsSymmetric a = Relation.IsSymmetric <{\x y w -> eqprop x y w}> EqualProp a
@-}
type IsSymmetric a = Relation.IsSymmetric EqualProp a

{-@
type IsTransitive a = Relation.IsTransitive <{\x y w -> eqprop x y w}> EqualProp a
@-}
type IsTransitive a = Relation.IsTransitive EqualProp a

{-
## Instances
-}

{-@
isReflexive_base :: Equality.SMT.IsReflexive a -> IsReflexive a
@-}
isReflexive_base :: Equality.SMT.IsReflexive a -> IsReflexive a

isReflexive Equality.SMT.IsReflexive =
  IsReflexive
    ( \x ->
        let eSMTxx = reflexivity Equality.SMT.IsReflexive x
         in SMT x x eSMTxx
    )

-- TODO: implement
{-@
isReflexive_induct :: IsReflexive b -> IsReflexive (a -> b)
@-}
isReflexive_induct :: IsReflexive b -> IsReflexive (a -> b)
isReflexive_induct = undefined

-- TODO: implement
{-@
isSymmetricEqualProp_base :: Equality.SMT.IsSymmetric a -> IsSymmetric a
@-}
isSymmetricEqualProp_base :: Equality.SMT.IsSymmetric a -> IsSymmetric a
isSymmetricEqualProp_base = undefined

-- TODO: implement
{-@
isSymmetricEqualProp_induct ::
  IsSymmetric b -> IsSymmetric (a -> b)
@-}
isSymmetricEqualProp_induct ::
  IsSymmetric b -> IsSymmetric (a -> b)
isSymmetricEqualProp_induct = undefined

-- TODO: implement
{-@
isTransitiveEqualProp_base :: Equality.SMT.IsTransitive a -> IsTransitive a
@-}
isTransitiveEqualProp_base :: Equality.SMT.IsTransitive a -> IsTransitive a
isTransitiveEqualProp_base = undefined

-- TODO: implement
{-@
isTransitiveEqualProp_induct ::
  Equality.SMT.IsTransitive b -> IsTransitive (a -> b)
@-}
isTransitiveEqualProp_induct ::
  Equality.SMT.IsTransitive b -> IsTransitive (a -> b)
isTransitiveEqualProp_induct = undefined

-- TODO: implement
{-@
isEqualityEqualProp_base :: Equality.SMT.IsEquality a -> IsEquality a
@-}
isEqualityEqualProp_base :: Equality.SMT.IsEquality a -> IsEquality a
isEqualityEqualProp_base = undefined

-- TODO: implement
{-@
isEqualityEqualProp_induct ::
  Equality.SMT.IsEquality b -> IsEquality (a -> b)
@-}
isEqualityEqualProp_induct ::
  Equality.SMT.IsEquality b -> IsEquality (a -> b)
isEqualityEqualProp_induct = undefined
