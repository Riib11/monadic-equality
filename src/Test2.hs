module Test2 where

{-
# Proof
-}

type Proof = ()

{-@ reflect trivial @-}
trivial :: Proof
trivial = ()

{-
# Relation
-}

{-@
type Re r a RE X Y = {_:r a | RE X Y}
@-}

{-@
data IsReflexive r a <re :: a -> a -> Bool> = IsReflexive
  { reflexivity :: x:a ->
      Re r a {re} {x} {x}
  }
@-}
data IsReflexive r a = IsReflexive (a -> r a)

{-@
data IsSymmetric r a <re :: a -> a -> Bool> = IsSymmetric
  { symmetry :: x:a -> y:a ->
      Re r a {re} {x} {y} ->
      Re r a {re} {y} {x}
  }
@-}
data IsSymmetric r a = IsSymmetric (a -> a -> r a -> r a)

{-@
data IsTransitive r a <re :: a -> a -> Bool> = IsTransitive
  { transitivity :: x:a -> y:a -> z:a ->
      Re r a {re} {x} {y} ->
      Re r a {re} {y} {z} ->
      Re r a {re} {x} {z}
  }
@-}
data IsTransitive r a = IsTransitive (a -> a -> a -> r a -> r a -> r a)

{-
# Equality
-}

{-@
type Eq e a EQ X Y = {_:e a | EQ X Y}
@-}

{-@
data IsEquality e a <eq :: a -> a -> Bool> = IsEquality
  { isReflexive :: IsReflexive <{\x y -> eq x y}> e a,
    isSymmetric :: IsSymmetric <{\x y -> eq x y}> e a,
    isTransitive :: IsTransitive <{\x y -> eq x y}> e a
  }
@-}
data IsEquality e a
  = IsEquality
      (IsReflexive e a)
      (IsSymmetric e a)
      (IsTransitive e a)

{-@
data Equality e a = Equality
  { eq :: a -> a -> Bool,
    isEquality :: IsEquality <{\x y -> eq x y}> e a
  }
@-}
data Equality e a = Equality
  { eq :: a -> a -> Bool,
    isEquality :: IsEquality e a
  }

{-
# SMT Equality
-}

{-@ measure eqSMT :: a -> a -> Bool @-}
eqSMT :: a -> a -> Bool
eqSMT = undefined

-- -- TODO: temp
-- {-@ reflect eqSMT @-}
-- eqSMT :: a -> a -> Bool
-- eqSMT _ _ = True

{-@
type EqSMT a X Y = Eq EqualSMT a {eqSMT} {X} {Y}
@-}

{-@
data EqualSMT :: * -> * where
  SMT ::
    x:a -> y:a ->
    {_:Proof | x = y} ->
    EqSMT a {x} {y}
@-}
data EqualSMT :: * -> * where
  SMT :: a -> a -> Proof -> EqualSMT a

{-@
toEqualSMT :: x:a -> y:a -> {_:Proof | x = y} -> EqSMT a {x} {y}
@-}
toEqualSMT :: a -> a -> Proof -> EqualSMT a
toEqualSMT x y e = SMT x y e

{-@
assume fromEqualSMT :: x:a -> y:a -> EqSMT a {x} {y} -> {x = y}
@-}
fromEqualSMT :: a -> a -> EqualSMT a -> Proof
fromEqualSMT x y (SMT _x _y e) = undefined

{-
## Instances
-}

-- {-@
-- type IsEqualitySMT a = IsEquality <{\x y -> eqSMT x y}> EqSMT a
-- @-}
-- type IsEqualitySMT a = IsEquality EqSMT a

-- {-@
-- type EqualitySMT a = Equality EqualSMT
-- @-}

{-
isReflexiveSMT
isSymmetricSMT
isTransitiveSMT
isEqualitySMT
equalitySMT
-}

{-
### Bool
-}

{-@
measure eqBool :: x:Bool -> y:Bool -> {v:Bool | v <=> eqSMT x y}
@-}
eqBool :: Bool -> Bool -> Bool
eqBool True True = True
eqBool False False = True
eqBool _ _ = False

{-@
isReflexiveSMT_Bool :: IsReflexive <{\x y -> eqSMT x y}> EqualSMT Bool
@-}
isReflexiveSMT_Bool :: IsReflexive EqualSMT Bool
isReflexiveSMT_Bool = IsReflexive (\x -> SMT x x trivial)

-- where
--   e x = SMT x x trivial

{-@
isSymmetricSMT_Bool :: IsSymmetric <{\x y -> eqSMT x y}> EqualSMT Bool
@-}
isSymmetricSMT_Bool :: IsSymmetric EqualSMT Bool
isSymmetricSMT_Bool = IsSymmetric e
  where
    {-@
    assume e :: x:Bool -> y:Bool ->
      {_:EqualSMT Bool | eqSMT x y} ->
      {_:EqualSMT Bool | eqSMT y x}
    @-}
    e :: Bool -> Bool -> EqualSMT Bool -> EqualSMT Bool
    e = undefined

-- e x y e' = SMT y x (fromEqualSMT x y e')

-- Eq e a EQ X Y = {_:e a | EQ X Y}
-- EqSMT e a X Y = Eq EqualSMT a {eqSMT} {X} {Y}

{-
## Properties
-}

-- {-@
-- assume equalitySMT :: Equality EqualSMT a
-- @-}
-- equalitySMT :: Equality EqualSMT a
-- equalitySMT = undefined

-- {-@
-- assume isEquality_EqualSMT :: IsEquality <{\x y -> eqSMT x y}> EqualSMT a
-- @-}
-- isEquality_EqualSMT :: IsEquality EqualSMT a
-- isEquality_EqualSMT = undefined

-- {-@
-- assume isReflexive_EqualSMT :: IsReflexive <{\x y -> eqSMT x y}> EqualSMT a
-- @-}
-- isReflexive_EqualSMT :: IsReflexive EqualSMT a
-- isReflexive_EqualSMT = undefined

-- {-@
-- assume isSymmetric_EqualSMT :: IsSymmetric <{\x y -> eqSMT x y}> EqualSMT a
-- @-}
-- isSymmetric_EqualSMT :: IsSymmetric EqualSMT a
-- isSymmetric_EqualSMT = undefined

-- {-@
-- assume isTransitive_EqualSMT :: IsTransitive <{\x y -> eqSMT x y}> EqualSMT a
-- @-}
-- isTransitive_EqualSMT :: IsTransitive EqualSMT a
-- isTransitive_EqualSMT = undefined

{-
# Propositional Equality
-}

{-@
measure eqprop :: a -> a -> Bool
@-}
eqprop :: a -> a -> Bool
eqprop = undefined

{-@
type EqProp a X Y = Eq EqualProp a {eqprop} {X} {Y}
@-}

{-@
data EqualProp :: * -> * where
    LiftEqualitySMT ::
      x:a -> y:a ->
      EqSMT a {x} {y} ->
      EqProp a {x} {y}
  | Extensionality ::
      f:(a -> b) -> g:(a -> b) ->
      (x:a -> EqProp b {f x} {g x}) ->
      EqProp (a -> b) {f} {g}
  | Congruency ::
      x:a -> y:a -> c:(a -> b) ->
      EqProp a {x} {y} ->
      EqProp b {c x} {c y}
@-}
data EqualProp :: * -> * where
  LiftEqualitySMT :: a -> a -> EqualSMT a -> EqualProp a
  Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualProp b) -> EqualProp (a -> b)
  Congruency :: a -> a -> (a -> b) -> EqualProp a -> EqualProp b

-- TODO

-- {-@
-- toEqualProp :: x:a -> y:a -> EqSMT a {x} {y} -> EqProp a {x} {y}
-- @-}
-- toEqualProp :: a -> a -> EqualSMT a -> EqualProp a
-- toEqualProp x y e = LiftEqualitySMT x y e

-- {-@
-- fromEqualProp :: x:a -> y:a -> IsEquality <{\x y -> eqSMT x y}> EqSMT a ->
--   EqProp a {x} {y} ->
--   EqSMT a {x} {y}
-- @-}
-- fromEqualProp :: a -> a -> Equality EqualSMT a ->
