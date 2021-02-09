module Test5 where

import Proof
import Prelude hiding (Eq)

{-
Useful
-}

{-@
data IsProduct a b = IsProduct
  { proj1 :: a -> b,
    proj2 :: a -> b
  }
@-}
data IsProduct a b = IsProduct
  { proj1 :: a -> b,
    proj2 :: a -> b
  }

{-
# Relation
-}

{-@
data IsRelation r a = IsRelation
  {isProduct :: IsProduct (r a) a}
@-}
data IsRelation r a = IsRelation
  {isProduct :: IsProduct (r a) a}

{-@
data Relation r a = Relation
  { re :: a -> a -> Bool,
    isRelation :: IsRelation r a
  }
@-}
data Relation r a = Relation
  { re :: a -> a -> Bool,
    isRelation :: IsRelation r a
  }

{-@ reflect relation_proj1 @-}
relation_proj1 :: IsRelation r a -> r a -> a
relation_proj1 isRelation = proj1 (isProduct isRelation)

{-@ reflect relation_proj2 @-}
relation_proj2 :: IsRelation r a -> r a -> a
relation_proj2 isRelation = proj2 (isProduct isRelation)

{-@
type Rel r a ISRELATION X Y =
  {w:r a | X = relation_proj1 ISRELATION w && Y = relation_proj2 ISRELATION w}
@-}
type Rel r a = r a

{-@
data IsReflexive r a = IsReflexive
  { reflexivity :: isRelation:IsRelation r a ->
      x:a ->
      Rel r a {isRelation} {x} {x} }
@-}
data IsReflexive r a = IsReflexive
  {reflexivity :: IsRelation r a -> a -> Rel r a}

{-@
data IsSymmetric r a = IsSymmetric
  { symmetry :: isRelation:IsRelation r a ->
      x:a -> y:a ->
      Rel r a {isRelation} {x} {y} ->
      Rel r a {isRelation} {y} {x} }
@-}
data IsSymmetric r a = IsSymmetric
  {symmetry :: IsRelation r a -> a -> a -> Rel r a -> Rel r a}

{-@
data IsTransitive r a = IsTransitive
  { transitivity :: isRelation:IsRelation r a ->
      x:a -> y:a -> z:a ->
      Rel r a {isRelation} {x} {y} ->
      Rel r a {isRelation} {y} {z} ->
      Rel r a {isRelation} {x} {z} }
@-}
data IsTransitive r a = IsTransitive
  {transitivity :: IsRelation r a -> a -> a -> a -> Rel r a -> Rel r a -> Rel r a}

{-
# Equality
-}

{-@
type Eq e a ISEQUALITY X Y = Rel e a {isRelation ISEQUALITY} {X} {Y}
@-}
type Eq e a = Rel e a

{-@
data IsEquality e a = IsEquality
  { isRelation :: IsRelation e a,
    isReflexive :: IsReflexive e a,
    isSymmetric :: IsSymmetric e a,
    isTransitive :: IsTransitive e a
  }
@-}
data IsEquality e a = IsEquality
  { isRelation :: IsRelation e a,
    isReflexive :: IsReflexive e a,
    isSymmetric :: IsSymmetric e a,
    isTransitive :: IsTransitive e a
  }

equality_

{-@
data Equality e a = Equality
  { eq :: a -> a -> Bool,
    isEquality :: IsEquality e a
  }
@-}
data Equality e a = Equality
  { eq :: a -> a -> Bool,
    isEquality :: IsEquality e a
  }

-- {-
-- # SMT Equality
-- -}

-- {-@ reflect isBinary_EqualSMT @-}
-- isBinary_EqualSMT :: IsProduct (EqualSMT a) a
-- isBinary_EqualSMT =
--   IsProduct
--     { proj1 = \(SMT x _ _) -> x,
--       proj2 = \(SMT _ y _) -> y
--     }

-- {-@
-- type EqSMT a X Y =
--   {w:EqualSMT a | X = proj1 isBinary_EqualSMT w && Y = proj2 isBinary_EqualSMT w}
-- @-}

-- {-@
-- data EqualSMT :: * -> * where
--   SMT ::
--     x:a -> y:a ->
--     {_:Proof | x = y} ->
--     EqSMT a {x} {y}
-- @-}
-- data EqualSMT :: * -> * where
--   SMT :: a -> a -> Proof -> EqualSMT a

-- {-@
-- toEqualSMT :: x:a -> y:a -> {_:Proof | x = y} -> EqSMT a {x} {y}
-- @-}
-- toEqualSMT :: a -> a -> Proof -> EqualSMT a
-- toEqualSMT = SMT

-- {-@
-- fromEqualSMT :: x:a -> y:a -> EqSMT a {x} {y} -> {x = y}
-- @-}
-- fromEqualSMT :: a -> a -> EqualSMT a -> Proof
-- fromEqualSMT _ _ eSMT@(SMT _ _ e) = e

-- TODO: old

-- {-
-- ## Instances
-- -}

-- -- {-@
-- -- type IsEqualitySMT a = IsEquality <{\x y -> eqSMT x y}> EqSMT a
-- -- @-}
-- -- type IsEqualitySMT a = IsEquality EqSMT a

-- -- {-@
-- -- type EqualitySMT a = Equality EqualSMT
-- -- @-}

-- {-
-- isReflexiveSMT
-- isSymmetricSMT
-- isTransitiveSMT
-- isEqualitySMT
-- equalitySMT
-- -}

-- {-
-- ### Bool
-- -}

-- {-@
-- measure eqBool :: x:Bool -> y:Bool -> {v:Bool | v <=> eqSMT x y}
-- @-}
-- eqBool :: Bool -> Bool -> Bool
-- eqBool True True = True
-- eqBool False False = True
-- eqBool _ _ = False

-- {-@
-- isReflexiveSMT_Bool :: IsReflexive <{\x y -> eqSMT x y}> EqualSMT Bool
-- @-}
-- isReflexiveSMT_Bool :: IsReflexive EqualSMT Bool
-- isReflexiveSMT_Bool = IsReflexive (\x -> SMT x x trivial)

-- -- TODO
-- -- {-@
-- -- assume isSymmetricSMT_Bool :: IsSymmetric <{\x y -> eqSMT x y}> EqualSMT Bool
-- -- @-}
-- -- isSymmetricSMT_Bool :: IsSymmetric EqualSMT Bool
-- -- isSymmetricSMT_Bool = IsSymmetric e
-- --   where
-- --     {-@
-- --     assume e :: x:Bool -> y:Bool ->
-- --       {_:EqualSMT Bool | eqSMT x y} ->
-- --       {_:EqualSMT Bool | eqSMT y x}
-- --     @-}
-- --     e :: Bool -> Bool -> EqualSMT Bool -> EqualSMT Bool
-- --     e = undefined

-- {-
-- ## Properties
-- -}

-- -- {-@
-- -- assume equalitySMT :: Equality EqualSMT a
-- -- @-}
-- -- equalitySMT :: Equality EqualSMT a
-- -- equalitySMT = undefined

-- -- {-@
-- -- assume isEquality_EqualSMT :: IsEquality <{\x y -> eqSMT x y}> EqualSMT a
-- -- @-}
-- -- isEquality_EqualSMT :: IsEquality EqualSMT a
-- -- isEquality_EqualSMT = undefined

-- -- {-@
-- -- assume isReflexive_EqualSMT :: IsReflexive <{\x y -> eqSMT x y}> EqualSMT a
-- -- @-}
-- -- isReflexive_EqualSMT :: IsReflexive EqualSMT a
-- -- isReflexive_EqualSMT = undefined

-- -- {-@
-- -- assume isSymmetric_EqualSMT :: IsSymmetric <{\x y -> eqSMT x y}> EqualSMT a
-- -- @-}
-- -- isSymmetric_EqualSMT :: IsSymmetric EqualSMT a
-- -- isSymmetric_EqualSMT = undefined

-- -- {-@
-- -- assume isTransitive_EqualSMT :: IsTransitive <{\x y -> eqSMT x y}> EqualSMT a
-- -- @-}
-- -- isTransitive_EqualSMT :: IsTransitive EqualSMT a
-- -- isTransitive_EqualSMT = undefined

-- {-
-- # Propositional Equality
-- -}

-- {-@
-- measure eqprop :: a -> a -> Bool
-- @-}
-- eqprop :: a -> a -> Bool
-- eqprop = undefined

-- {-@
-- type EqProp a X Y = Eq EqualProp a {eqprop} {X} {Y}
-- @-}

-- {-@
-- data EqualProp :: * -> * where
--     LiftEqualitySMT ::
--       x:a -> y:a ->
--       EqSMT a {x} {y} ->
--       EqProp a {x} {y}
--   | Extensionality ::
--       f:(a -> b) -> g:(a -> b) ->
--       (x:a -> EqProp b {f x} {g x}) ->
--       EqProp (a -> b) {f} {g}
--   | Congruency ::
--       x:a -> y:a -> c:(a -> b) ->
--       EqProp a {x} {y} ->
--       EqProp b {c x} {c y}
-- @-}
-- data EqualProp :: * -> * where
--   LiftEqualitySMT :: a -> a -> EqualSMT a -> EqualProp a
--   Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualProp b) -> EqualProp (a -> b)
--   Congruency :: a -> a -> (a -> b) -> EqualProp a -> EqualProp b

-- -- TODO

-- -- {-@
-- -- toEqualProp :: x:a -> y:a -> EqSMT a {x} {y} -> EqProp a {x} {y}
-- -- @-}
-- -- toEqualProp :: a -> a -> EqualSMT a -> EqualProp a
-- -- toEqualProp x y e = LiftEqualitySMT x y e

-- -- {-@
-- -- fromEqualProp :: x:a -> y:a -> IsEquality <{\x y -> eqSMT x y}> EqSMT a ->
-- --   EqProp a {x} {y} ->
-- --   EqSMT a {x} {y}
-- -- @-}
-- -- fromEqualProp :: a -> a -> Equality EqualSMT a ->
