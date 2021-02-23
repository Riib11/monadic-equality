module Relation.Equality.SMT where

import ProofCombinators
import Relation.Equality.Prim

-- {-
-- # SMT Equality
-- -}

-- {-
-- ## Definition
-- -}

-- {-@
-- measure eqsmt :: a -> a -> EqualitySMT a -> Bool
-- @-}

-- {-@
-- type EqualSMT a X Y = {w:EqualitySMT a | eqsmt X Y w}
-- @-}

-- {-@
-- data EqualitySMT :: * -> * where
--   FromEqualityPrim :: Concrete_EqualitySMT a => x:a -> y:a -> {_:Proof | x = y} -> EqualSMT a {x} {y}
-- @-}
-- data EqualitySMT :: * -> * where
--   FromEqualityPrim :: Concrete_EqualitySMT a => a -> a -> Proof -> EqualitySMT a

-- {-@
-- toEqualitySMT :: Concrete_EqualitySMT a => x:a -> y:a -> {_:Proof | x = y} -> {w:EqualitySMT a | eqsmt x y w}
-- @-}
-- toEqualitySMT :: Concrete_EqualitySMT a => a -> a -> Proof -> EqualitySMT a
-- toEqualitySMT x y e = FromEqualityPrim x y e

-- {-
-- ## Properties
-- -}

-- {-
-- ### Concreteness
-- -}

-- -- must be instantiated for each instance of concrete SMT equality
-- {-@
-- class Concrete_EqualitySMT a where
--   concreteness_EqualitySMT :: x:a -> y:a -> EqualSMT a {x} {y} -> {_:Proof | x = y}
-- @-}
-- class Concrete_EqualitySMT a where
--   concreteness_EqualitySMT :: a -> a -> EqualitySMT a -> Proof

-- {-
-- ### Reflexivity
-- -}

-- {-@
-- class Reflexive_EqualitySMT a where
--   reflexivity_EqualitySMT :: x:a -> EqualSMT a {x} {x}
-- @-}
-- class Reflexive_EqualitySMT a where
--   reflexivity_EqualitySMT :: a -> EqualitySMT a

-- instance Concrete_EqualitySMT a => Reflexive_EqualitySMT a where
--   reflexivity_EqualitySMT x =
--     let e_x_x = reflexivity_EqualityPrim x
--      in FromEqualityPrim x x e_x_x

-- {-
-- ### Symmetry
-- -}

-- {-@
-- class Symmetric_EqualitySMT a where
--   symmetry_EqualitySMT :: x:a -> y:a -> EqualSMT a {x} {y} -> EqualSMT a {y} {x}
-- @-}
-- class Symmetric_EqualitySMT a where
--   symmetry_EqualitySMT :: a -> a -> EqualitySMT a -> EqualitySMT a

-- instance Concrete_EqualitySMT a => Symmetric_EqualitySMT a where
--   symmetry_EqualitySMT x y eSMT_x_y =
--     let e_x_y = concreteness_EqualitySMT x y eSMT_x_y
--         e_y_x = symmetry_EqualityPrim x y e_x_y
--      in FromEqualityPrim y x e_y_x

-- {-
-- ### Transitivity
-- -}

-- {-@
-- class Transitive_EqualitySMT a where
--   transitivity_EqualitySMT :: x:a -> y:a -> z:a -> EqualSMT a {x} {y} -> EqualSMT a {y} {z} -> EqualSMT a {x} {z}
-- @-}
-- class Transitive_EqualitySMT a where
--   transitivity_EqualitySMT :: a -> a -> a -> EqualitySMT a -> EqualitySMT a -> EqualitySMT a

-- instance Concrete_EqualitySMT a => Transitive_EqualitySMT a where
--   transitivity_EqualitySMT x y z eSMT_x_y eSMT_y_z =
--     let e_x_y = concreteness_EqualitySMT x y eSMT_x_y
--         e_y_z = concreteness_EqualitySMT y z eSMT_y_z
--         e_x_z = e_x_y &&& e_y_z
--      in FromEqualityPrim x z e_x_z

-- {-
-- ### Substitutability
-- -}

-- {-@
-- class Substitutitive_EqualitySMT a b where
--   substitutability_EqualitySMT :: x:a -> y:a -> c:(a -> b) -> EqualSMT a {x} {y} -> EqualSMT b {c x} {c y}
-- @-}
-- class Substitutitive_EqualitySMT a b where
--   substitutability_EqualitySMT :: a -> a -> (a -> b) -> EqualitySMT a -> EqualitySMT b

-- instance (Concrete_EqualitySMT a, Concrete_EqualitySMT b) => Substitutitive_EqualitySMT a b where
--   substitutability_EqualitySMT x y c eSMT_x_y =
--     let e_x_y = concreteness_EqualitySMT x y eSMT_x_y
--         e_cx_cy = substitutability_Prim x y c e_x_y
--      in FromEqualityPrim (c x) (c y) e_cx_cy
