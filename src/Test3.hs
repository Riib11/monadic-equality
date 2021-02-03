module Test3 where

{-
# Proof
-}

type Proof = ()

{-@ reflect trivial @-}
trivial :: Proof
trivial = ()

{-
# Axiomatic Equality
-}

-- {-@
-- class EqualityAxiomatic a where
--   eqax :: x:a -> y:a -> Bool
--   eqax_reflexivity :: x:a ->
--     {eqax x x}
--   eqax_symmetry :: x:a -> y:a ->
--     {eqax x y => eqax y x}
--   eqax_transitivity :: x:a -> y:a -> z:a ->
--     {(eqax x y && eqax y z) => eqax x z}
-- @-}
-- class EqualityAxiomatic a where
--   eqax :: a -> a -> Bool
--   eqax_reflexivity :: a -> Proof
--   eqax_symmetry :: a -> a -> Proof
--   eqax_transitivity :: a -> a -> a -> Proof

-- -- {-@
-- -- data EqualityAxiomatic a = Equality
-- --   { eqax :: x:a -> y:a -> Bool,
-- --     eqax_reflexivity :: x:a ->
-- --       {eqax x x},
-- --     eqax_symmetry :: x:a -> y:a ->
-- --       {eqax x y => eqax y x},
-- --     eqax_transitivity :: x:a -> y:a -> z:a ->
-- --       {(eqax x y && eqax y z) => eqax x z}
-- --   }
-- -- @-}
-- -- data EqualityAxiomatic a = Equality
-- --   { eqax :: a -> a -> Bool,
-- --     eqax_reflexivity :: a -> Proof,
-- --     eqax_symmetry :: a -> a -> Proof,
-- --     eqax_transitivity :: a -> a -> a -> Proof
-- --   }

-- {-
-- # Propositional Equality
-- -}

-- {-@
-- measure eqprop :: a -> a -> Bool
-- @-}

-- {-@
-- type EqProp a X Y = {_:EqualityProp a | eqprop X Y}
-- @-}

-- {-@
-- data EqualityProp :: * -> * where
--     Axiomatic :: EqualityAxiomatic a => x:a -> y:a ->
--       {_:Proof | eqax x y} ->
--       EqProp a {x} {y}
--   | Extensionality :: f:(a -> b) -> g:(a -> b) ->
--       (x:a -> EqProp b {f x} {g x}) ->
--       EqProp (a -> b) {f} {g}
--   | Congruency :: x:a -> y:a -> c:(a -> b) ->
--       EqProp a {x} {y} ->
--       EqProp b {c x} {c y}
-- @-}
-- data EqualityProp :: * -> * where
--   Axiomatic :: EqualityAxiomatic a => a -> a -> Proof -> EqualityProp a
--   Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
--   Congruency :: a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

-- {-
-- # Equivalence Properties
-- -}

-- {-@
-- class Reflexivity a where
--   reflexivity :: x:a -> EqProp a {x} {x}
-- @-}
-- class Reflexivity a where
--   reflexivity :: a -> EqualityProp a

-- instance EqualityAxiomatic a => Reflexivity a where
--   reflexivity x = Axiomatic x x (eqax_reflexivity x)

-- instance Reflexivity b => Reflexivity (a -> b) where
--   reflexivity f = Extensionality f f (\x -> reflexivity (f x))

-- {-@
-- newtype Reflexivity a = Reflexivity
--   {reflexivity :: x:a -> EqProp a {x} {x}}
-- @-}
-- newtype Reflexivity a = Reflexivity
--   {reflexivity :: a -> EqualityProp a}

-- -- base case
-- {-@
-- equality_reflexivity_base :: EqualityAxiomatic a -> Reflexivity a
-- @-}
-- equality_reflexivity_base :: EqualityAxiomatic a -> Reflexivity a
-- equality_reflexivity_base iEqualityAxiomatic =
--   Reflexivity
--     { reflexivity = equality_reflexive_base_aux iEqualityAxiomatic
--     }

-- {-@
-- equality_reflexive_base_aux :: EqualityAxiomatic a -> x:a -> EqProp a {x} {x}
-- @-}
-- equality_reflexive_base_aux :: forall a. EqualityAxiomatic a -> a -> EqualityProp a
-- equality_reflexive_base_aux iEqualityAxiomatic x =
--   Axiomatic iEqualityAxiomatic x x (eqax_reflexivity iEqualityAxiomatic x)

-- -- inductive step
-- {-@
-- equality_reflexivity_induction ::
--   Reflexivity b -> Reflexivity (a -> b)
-- @-}
-- equality_reflexivity_induction ::
--   Reflexivity b -> Reflexivity (a -> b)
-- equality_reflexivity_induction iReflexivity =
--   Reflexivity
--     { reflexivity = equality_reflexivity_induction_aux iReflexivity
--     }

-- {-@
-- equality_reflexivity_induction_aux ::
--   Reflexivity b -> (a -> b) -> EqualityProp (a -> b)
-- @-}
-- equality_reflexivity_induction_aux ::
--   Reflexivity b -> (a -> b) -> EqualityProp (a -> b)
-- equality_reflexivity_induction_aux iReflexivity f =
--   Extensionality f f (\x -> reflexivity iReflexivity (f x))
