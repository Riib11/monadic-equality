module Equality.Prop where

import Equality
import Proof
import Relation

-- {-
-- # Propsitional Equality

-- TODO
-- -}

-- {-@ measure eqprop :: a -> a -> Bool @-}

-- {-@
-- assume eqprop_isReflexive :: IsReflexive a {eqprop}
-- @-}
-- eqprop_isReflexive :: IsReflexive a
-- eqprop_isReflexive x = ()

-- {-@
-- assume eqprop_isSymmetric :: IsSymmetric a {eqprop}
-- @-}
-- eqprop_isSymmetric :: IsSymmetric a
-- eqprop_isSymmetric x y = ()

-- {-@
-- assume eqprop_isTransitive :: IsTransitive a {eqprop}
-- @-}
-- eqprop_isTransitive :: IsTransitive a
-- eqprop_isTransitive x y z = ()

-- {-@
-- type EqProp a X Y = {_:EqualityProp a | eqprop X Y}
-- @-}

-- {-@
-- data EqualityProp :: * -> * where
--     BEq ::
--       equality:Equality a ->
--       x:a -> y:a -> {_:Proof | eq equality x y} ->
--       EqProp a {x} {y}
--   | XEq ::
--       f:(a -> b) -> g:(a -> b) ->
--       (x:a -> EqProp b {f x} {g x}) ->
--       EqProp (a -> b) {f} {g}
--   | CEq ::
--       x:a -> y:a -> EqProp a {x} {y} ->
--       ctx:(a -> b) -> EqProp b {ctx x} {ctx y}
-- @-}
-- data EqualityProp :: * -> * where
--   BEq :: Equality a -> a -> a -> Proof -> EqualityProp a
--   XEq :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
--   CEq :: a -> a -> EqualityProp a -> (a -> b) -> EqualityProp b

-- {-
-- # Equational Reasoning
-- -}

-- infixl 3 ===

-- {-@
-- (===) ::
--   xp:(a, EqualityProp a) ->
--   {yp:(a, EqualityProp a) | eqprop (fst xp) (fst yp)} ->
--   {zp:(a, EqualityProp a) | eqprop (fst xp) (fst zp) && eqprop (fst yp) (fst zp)}
-- @-}
-- (===) :: (a, EqualityProp a) -> (a, EqualityProp a) -> (a, EqualityProp a)
-- _ === (y, p) = (y, p) `withProof` eqprop_isReflexive y

-- -- {-@
-- -- data XEquality a <eq :: a -> a -> Bool> = XEquality
-- --   { isXReflexive :: IsXReflexive a <eq>}
-- -- @-}
-- -- data XEquality a = XEquality
-- --   {isXReflexive :: IsXReflexive a}

-- -- {-@
-- -- eta_equivalence :: f:(a -> b) ->
-- --   {EqProp (a -> b) {f} {\x -> f x}}
-- -- @-}
-- -- eta_equivalence :: (a -> b) -> EqualityProp (a -> b)
-- -- eta_equivalence f =
-- --   (f, BEq )
-- --     === ()
-- --     *** QED

-- -- OLD

-- -- {-@
-- -- (===) :: x:a -> {y:a | eqprop x y} -> {z:a | eqprop x z && eqprop y z}
-- -- @-}
-- -- (===) :: a -> a -> a
-- -- _ === y = y `withProof` eqprop_isReflexive y
-- -- {-# INLINE (===) #-}

-- -- infixl 2 ?

-- -- {-@
-- -- (?) :: forall a b <y :: a>. x:a -> {_:EqualityProp a | eqprop x y} -> {x:a | eqprop x y}
-- -- @-}
-- -- (?) :: a -> EqualityProp a -> a
-- -- x ? _ = x
