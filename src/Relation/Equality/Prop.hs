module Relation.Equality.Prop where

import ProofCombinators
import Relation
import Relation.Equality
import Relation.Equality.SMT

-- {-
-- # Propositional Equality
-- -}

-- -- Measure. Uninterpreted measure for propositional equality.
-- {-@
-- measure eqprop :: x:a -> y:a -> EqualProp a -> Bool
-- @-}

-- -- Type Synonym. Witness to `a`-equality between `X` and `Y`.
-- {-@
-- type EqProp a X Y = (EqualProp a)<eqprop X Y>
-- @-}

-- -- Inductive Datatype.
-- {-@
-- data EqualProp :: * -> * where
--     InjectSMT ::
--       x:a -> y:a ->
--       EqSMT a {x} {y} ->
--       EqProp a {x} {y}
--   | Extensionality ::
--       f:(a -> b) -> g:(a -> b) ->
--       (x:a -> EqProp a {f x} {g x}) ->
--       EqProp a {f} {g}
--   | Substitution ::
--       x:a -> y:a -> c:(a -> b) ->
--       EqProp a {x} {y} ->
--       EqProp b {f x} {f y}
-- @-}
-- data EqualProp :: * -> * where
--   InjectSMT :: a -> a -> EqualSMT a -> EqualProp a
--   Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualProp a) -> EqualProp a
--   Substitution :: a -> a -> (a -> b) -> EqualProp a -> EqualProp b

-- {-@
-- toEqualProp :: x:a -> y:a -> EqSMT a {x} {y} -> EqProp a {x} {y}
-- @-}
-- toEqualProp :: a -> a -> EqualSMT a -> EqualProp a
-- toEqualProp x y eSMT_x_y = InjectSMT

-- -- TODO: must this be assumed?
-- {-@
-- assume fromEqualProp :: x:a -> y:a -> EpProp a {x} {y} -> EqSMT a {x} {y}
-- @-}
-- fromEqualProp :: a -> a -> IsEquality EqualSMT a -> EqualProp a -> EqualSMT a
-- fromEqualProp x y isEqualityEqualSMT (InjectSMT _ _ eqSMT_x_y) = eqSMT_x_y

-- -- TODO
-- -- fromEqualProp x y isEqualityEqualSMT (Substitution _ _ c eqProp_cx_cy) = undefined

-- {-
-- ## Instances
-- -}

-- {-@
-- isReflexiveEqualProp_base ::
--   IsReflexive <{\x y w -> eqsmt x y w}> EqualSMT a ->
--   IsReflexive <{\x y w -> eqprop x y w}> EqualProp a
-- @-}
-- isReflexiveEqualProp_base ::
--   IsReflexive EqualSMT a ->
--   IsReflexive EqualProp a
-- isReflexiveEqualProp_base isReflexiveEqualSMT =
--   IsReflexive
--     ( \x ->
--         let eSMT_x_x = reflexivity isReflexiveEqualSMT x
--          in SMT x x eSMT_x_x
--     )

-- {-@
-- isReflexiveEqualProp_induct ::
--   IsReflexive <{\x y w -> eqprop x y w}> EqualProp b ->
--   IsReflexive <{\x y w -> eqprop x y w}> EqualProp (a -> b)
-- @-}
-- isReflexiveEqualProp_induct ::
--   IsReflexive EqualProp b ->
--   IsReflexive EqualProp (a -> b)
-- isReflexiveEqualProp_induct isReflexiveEqualProp =
--   IsReflexive
--     ( \f ->
--         let eProp_fx_fx x =
--               let eSMT_x_x = reflexivity isReflexiveEqualProp x
--                   eProp_x_x = InjectSMT x x eSMT_x_x
--                in Substitution x x f eProp_x_x
--          in Extensionality f f eProp_fx_fx
--     )

-- -- TODO: implement
-- {-@
-- isSymmetricEqualProp_base ::
--   IsSymmetric <{\x y w -> eqsmt x y w}> EqualSMT a ->
--   IsSymmetric <{\x y w -> eqprop x y w}> EqualProp a
-- @-}
-- isSymmetricEqualProp_base ::
--   IsSymmetric EqualSMT a ->
--   IsSymmetric EqualProp a
-- isSymmetricEqualProp_base isSymmetricEqualSMT = undefined

-- -- IsSymmetric (\x y eProp_x_y ->
-- --   let

-- --   )

-- -- TODO: implement
-- {-@
-- isSymmetricEqualProp_induct ::
--   IsSymmetric <{\x y w -> eqprop x y w}> EqualProp b ->
--   IsSymmetric <{\x y w -> eqprop x y w}> EqualProp (a -> b)
-- @-}
-- isSymmetricEqualProp_induct ::
--   IsSymmetric EqualProp b ->
--   IsSymmetric EqualProp (a -> b)
-- isSymmetricEqualProp_induct = undefined

-- -- TODO: implement
-- {-@
-- isTransitiveEqualProp_base ::
--   IsTransitive <{\x y w -> eqsmt x y w}> EqualSMT a ->
--   IsTransitive <{\x y w -> eqprop x y w}> EqualProp a
-- @-}
-- isTransitiveEqualProp_base ::
--   IsTransitive EqualSMT a ->
--   IsTransitive EqualProp a
-- isTransitiveEqualProp_base = undefined

-- -- TODO: implement
-- {-@
-- isTransitiveEqualProp_induct ::
--   IsTransitive <{\x y w -> eqprop x y w}> EqualProp b ->
--   IsTransitive <{\x y w -> eqprop x y w}> EqualProp (a -> b)
-- @-}
-- isTransitiveEqualProp_induct ::
--   IsTransitive EqualProp b ->
--   IsTransitive EqualProp (a -> b)
-- isTransitiveEqualProp_induct = undefined

-- -- TODO: add IsSubstitutive

-- -- TODO: implement
-- {-@
-- isEqualityEqualProp_base ::
--   IsEquality <{\x y w -> eqsmt x y w}> EqualSMT a ->
--   IsEquality <{\x y w -> eqprop x y w}> EqualProp a
-- @-}
-- isEqualityEqualProp_base ::
--   IsEquality EqualSMT a ->
--   IsEquality EqualProp a
-- isEqualityEqualProp_base = undefined

-- -- TODO: implement
-- {-@
-- isEqualityEqualProp_induct ::
--   IsEquality <{\x y w -> eqprop x y w}> EqualProp b ->
--   IsEquality <{\x y w -> eqprop x y w}> EqualProp (a -> b)
-- @-}
-- isEqualityEqualProp_induct ::
--   IsEquality EqualProp b ->
--   IsEquality EqualProp (a -> b)
-- isEqualityEqualProp_induct = undefined
