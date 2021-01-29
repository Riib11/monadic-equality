module Relation.Equality.Prop where

import Relation
import Relation.Equality
import Relation.Equality.SMT

{-
# Propositional Equality

-}

{-@ measure eqProp :: (a, a) -> Bool @-}
eqProp :: (a, a) -> Bool
eqProp = \_ -> True

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

isRelation_EqProp :: IsRelation EqProp a
isRelation_EqProp =
  IsRelation
    { decide = decide_EqProp,
      toWitness = toWitness_EqProp,
      fromWitness = fromWitness_EqProp,
      inversesToFromWitness = inversesToFromWitness_EqProp
    }

{-@ reflect decide_EqProp @-}
decide_EqProp :: (a, a) -> Bool
decide_EqProp = eqProp

{-@ reflect toWitness_EqProp @-}
toWitness_EqProp :: (a, a) -> EqProp a
toWitness_EqProp = undefined

{-@ reflect fromWitness_EqProp @-}
fromWitness_EqProp :: EqProp a -> (a, a)
fromWitness_EqProp = undefined

{-@ reflect inversesToFromWitness_EqProp @-}
inversesToFromWitness_EqProp :: ((a, a) -> (), r a -> ())
inversesToFromWitness_EqProp = undefined

-- isReflexive_EqProp :: IsReflexive EqProp a
-- isReflexive_EqProp = IsReflexive {}

-- isSymmetric_EqProp :: IsSymmetric EqProp a
-- isSymmetric_EqProp = IsSymmetric {}

-- isTransitive_EqProp :: IsTransitive EqProp a
-- isTransitive_EqProp = IsTransitive {}

-- -- Instance. EqProp is an equality on all types `a`.
-- {-@ reflect isEquality_EqProp @-}
-- isEquality_EqProp :: IsEquality EqProp a
-- isEquality_EqProp =
--   IsEquality
--     { equ_isRelation = _,
--       equ_isReflexive = _,
--       equ_isSymmetric = _,
--       equ_isTransitive = _
--     }
