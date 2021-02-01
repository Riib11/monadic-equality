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
newtype IsReflexive r a <re :: a -> a -> Bool> = IsReflexive
  { reflexivity :: x:a ->
      Re r a {re} {x} {x}
  }
@-}
newtype IsReflexive r a = IsReflexive (a -> r a)

{-@
newtype IsSymmetric r a <re :: a -> a -> Bool> = IsSymmetric
  { symmetry :: x:a -> y:a ->
      Re r a {re} {x} {y} ->
      Re r a {re} {y} {x}
  }
@-}
newtype IsSymmetric r a = IsSymmetric (a -> a -> r a -> r a)

{-@
newtype IsTransitive r a <re :: a -> a -> Bool> = IsTransitive
  { transitivity :: x:a -> y:a -> z:a ->
      Re r a {re} {x} {y} ->
      Re r a {re} {y} {z} ->
      Re r a {re} {x} {z}
  }
@-}
newtype IsTransitive r a = IsTransitive (a -> a -> a -> r a -> r a -> r a)

{-
# Equality
-}

{-@
type Eq e a EQ X Y = {_:e a | EQ X Y}
@-}

{-@
data IsEquality e a <eq :: a -> a -> Bool> = IsEquality
  { isReflexive :: IsReflexive e a <eq>,
    isSymmetric :: IsSymmetric e a <eq>,
    isTransitive :: IsTransitive e a <eq>
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
    isEquality :: IsEquality e a <eq>
  }
@-}
data Equality e a = Equality
  { eq :: a -> a -> Bool,
    isEquality :: IsEquality e a
  }

{-
# SMT Equality
-}

{-@ measure eqsmt :: a -> a -> Bool @-}
eqsmt :: a -> a -> Bool
eqsmt = undefined

-- {-@
-- type EqSMT a X Y = {_:EqualSMT a | eqsmt X Y}
-- @-}

{-@
type EqSMT a X Y = Eq EqualSMT a {eqsmt} {X} {Y}
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

-- {-@
-- isReflexive_eqsmt ::
-- @-}

-- {-@
-- sym :: x:a -> y:a -> {_:Proof | x = y} -> {_:Proof | y = x}
-- @-}
-- sym :: a -> a -> Proof -> Proof
-- sym x y exy = trivial

-- {-@
-- isReflexive_EqualSMT :: x:a -> EqSMT a {x} {x}
-- @-}
-- isReflexive_EqualSMT :: a -> EqualSMT a
-- isReflexive_EqualSMT x = SMT x x trivial

-- -- TODO: doesn't recognize that the x' and y' are the same as x and y,
-- -- by definition of SMT constructor
-- {-@
-- isSymmetric_EqualSMT :: x:a -> y:a ->
--   {_:EqualSMT a | eqsmt x y} ->
--   {_:EqualSMT a | eqsmt y x}
-- @-}
-- isSymmetric_EqualSMT :: a -> a -> EqualSMT a -> EqualSMT a
-- isSymmetric_EqualSMT x y (SMT x' y' exy) = SMT y x (sym x y exy)

-- where
--   {-@
--   pf :: x:a -> EqualSMT a {x} {x}
--   @-}
--   pf x = SMT x x ()

-- {-@
-- isEqualitySMT :: IsEquality EqualSMT a <eqsmt>
-- @-}
-- isEqualitySMT :: IsEquality EqualSMT a
-- isEqualitySMT = IsEquality
--   {

--   }
