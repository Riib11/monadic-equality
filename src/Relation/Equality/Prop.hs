module Relation.Equality.Prop where

import Relation
import Relation.Equality
import Relation.Equality.SMT

{-
# Propositional Equality

Propositional equality has three introduction rules:
- SMT equality of terms entails the propositional equality of the terms,
- extensional propositional equality of functions (i.e. the two have
  propositionally equal outputs given identical inputs) entails the
  propositional equality of the functions,
- contextual propositional equality of terms (i.e. renaming free names in the
  terms can yield propositional equality) entails the propositional equality of
  the terms.
-}

{-@ measure eqProp :: (a, a) -> Bool @-}

{-@
data EqProp where
    EqProp_SMT ::
      x:a -> y:a ->
      {_:() | x = y} ->
      {_:EqProp a | eqProp x y}
  | EqProp_Ext ::
      f:(a -> b) -> g:(a -> b) ->
      (x:a -> {_:EqProp b | eqProp (f x) (g x)}) ->
      {_:EqProp (a -> b) | eqProp f g}
  | EqProp_Ctx ::
      x:a -> y:a ->
      {_:EqProp a | eqProp x y} ->
      ctx:(a -> b) ->
      {_:EqProp b | eqProp (ctx x) (ctx y)}
@-}
data EqProp :: * -> * where
  EqProp_SMT :: a -> a -> () -> EqProp a
  EqProp_Ext :: (a -> b) -> (a -> b) -> (a -> EqProp b) -> EqProp (a -> b)
  EqProp_Ctx :: a -> a -> EqProp a -> (a -> b) -> EqProp b

-- Instance. `EqProp` is a relation on all types `a`.
{-@ assume isRelation_EqProp :: IsRelation EqProp a @-}
isRelation_EqProp :: IsRelation EqProp a
isRelation_EqProp = undefined

-- Property. `EqProp` is reflexive.
{-@ assume isReflexive_EqProp :: IsReflexive EqProp a @-}
isReflexive_EqProp :: IsReflexive EqProp a
isReflexive_EqProp = undefined

-- Property. `EqProp` is symmetric.
{-@ assume isSymmetric_EqProp :: IsSymmetric EqProp a @-}
isSymmetric_EqProp :: IsSymmetric EqProp a
isSymmetric_EqProp = undefined

-- Property. `EqProp` is transitive.
{-@ assume isTransitive_EqProp :: IsTransitive EqProp a @-}
isTransitive_EqProp :: IsTransitive EqProp a
isTransitive_EqProp = undefined

-- Instance. EqProp is an equality on all types `a`.
{-@ assume isEquality_EqProp :: IsEquality EqProp a @-}
isEquality_EqProp :: IsEquality EqProp a
isEquality_EqProp = undefined
