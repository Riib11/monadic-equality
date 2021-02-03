{-@ LIQUID "--ple-local" @-}

module Test4 where

{-
# Proof
-}

type Proof = ()

trivial :: Proof
trivial = ()

infixl 3 ***

{-@ assume (***) :: a -> p:QED -> { if (isAdmit p) then false else true } @-}
(***) :: a -> QED -> Proof
_ *** _ = ()

data QED = Admit | QED

{-@ measure isAdmit :: QED -> Bool @-}
{-@ Admit :: {v:QED | isAdmit v } @-}

infixl 3 ===

{-@ (===) :: x:a -> y:{a | y = x} -> {v:a | v = x && v = y} @-}
(===) :: a -> a -> a
_ === y = y

infixl 4 ?

{-@ (?) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b<pb> -> a<pa> @-}
(?) :: a -> b -> a
x ? _ = x
{-# INLINE (?) #-}

(&&&) :: Proof -> Proof -> Proof
x &&& _ = x

{-@ withProof :: x:a -> b -> {v:a | v = x} @-}
withProof :: a -> b -> a
withProof x _ = x

{-@ impossible :: {v:a | false} -> b @-}
impossible :: a -> b
impossible _ = undefined

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-
# Relation
-}

{-@ type IsReflexive a R = x:a -> {_:Proof | R x x} @-}
type IsReflexive a = a -> Proof

{-@ type IsSymmetric a R = x:a -> y:a -> {_:Proof | R x y => R y x} @-}
type IsSymmetric a = a -> a -> Proof

{-@ type IsTransitive a R = x:a -> y:a -> z:a -> {_:Proof | R x y && R y z => R x z} @-}
type IsTransitive a = a -> a -> a -> Proof

{-
# Equality
-}

{-@
data Equality a = Equality
  { eq :: a -> a -> Bool,
    eq_reflexivity :: IsReflexive a {eq},
    eq_symmetry :: IsSymmetric a {eq},
    eq_transitivity :: IsTransitive a {eq}
  }
@-}
data Equality a = Equality
  { eq :: a -> a -> Bool,
    eq_reflexivity :: IsReflexive a,
    eq_symmetry :: IsSymmetric a,
    eq_transitivity :: IsTransitive a
  }

{-
# Base Equalities
-}

{-
## Bool Equality
-}

{-@ reflect eqBool @-}
eqBool :: Bool -> Bool -> Bool
eqBool True True = True
eqBool False False = True
eqBool _ _ = False

{-@ automatic-instances eq_reflexivityBool @-}
{-@
eq_reflexivityBool :: IsReflexive Bool {eqBool}
@-}
eq_reflexivityBool :: IsReflexive Bool
eq_reflexivityBool _ = trivial

{-@ automatic-instances eq_symmetryBool @-}
{-@
eq_symmetryBool :: IsSymmetric Bool {eqBool}
@-}
eq_symmetryBool :: IsSymmetric Bool
eq_symmetryBool _ _ = trivial

{-@ automatic-instances eq_transitivityBool @-}
{-@
eq_transitivityBool :: IsTransitive Bool {eqBool}
@-}
eq_transitivityBool :: IsTransitive Bool
eq_transitivityBool _ _ _ = trivial

{-@
equalityBool :: Equality Bool
@-}
equalityBool :: Equality Bool
equalityBool =
  Equality
    { eq = eqBool,
      eq_reflexivity = eq_reflexivityBool,
      eq_symmetry = eq_symmetryBool,
      eq_transitivity = eq_transitivityBool
    }

{-
## Natural Number Equality
-}

{-@
data Natural = Zero | Suc Natural
@-}
data Natural = Zero | Suc Natural

-- {-@
-- measure sizeNatural :: Natural -> Int
-- @-}
-- sizeNatural :: Natural -> Int
-- sizeNatural Zero = 0
-- sizeNatural (Suc n) = 1 + sizeNatural n

{-@ reflect eqNatural @-}
eqNatural :: Natural -> Natural -> Bool
eqNatural Zero Zero = True
eqNatural (Suc m) (Suc n) = eqNatural m n
eqNatural _ _ = False

{-@ automatic-instances neq_Zero_Suc @-}
{-@
neq_Zero_Suc :: n:Natural -> {not (eqNatural (Suc n) Zero)}
@-}
neq_Zero_Suc :: Natural -> Proof
neq_Zero_Suc _ = trivial

-- {-@ automatic-instances eq_reflexivityNatural @-}
-- {-@
-- eq_reflexivityNatural :: x:Natural -> {_:Proof | eqNatural x x}
-- @-}
-- eq_reflexivityNatural :: IsReflexive Natural
-- eq_reflexivityNatural Zero = trivial
-- eq_reflexivityNatural (Suc n) = eq_reflexivityNatural n

-- {-@ automatic-instances eq_symmetryNatural @-}
-- {-@
-- eq_symmetryNatural :: IsSymmetric Natural {eqNatural}
-- @-}
-- eq_symmetryNatural :: IsSymmetric Natural
-- eq_symmetryNatural Zero Zero = trivial
-- eq_symmetryNatural (Suc _) Zero = trivial
-- eq_symmetryNatural Zero (Suc _) = trivial
-- eq_symmetryNatural (Suc m) (Suc n) = eq_symmetryNatural m n

-- {-@
-- eq_transitivityNatural :: IsTransitive Natural {eqNatural}
-- @-}
-- eq_transitivityNatural :: IsTransitive Natural
-- eq_transitivityNatural Zero Zero Zero = trivial
-- eq_transitivityNatural (Suc _) Zero Zero = trivial
-- eq_transitivityNatural Zero (Suc m) Zero =
--   (eqNatural Zero (Suc m) && eqNatural (Suc m) Zero)
--     === (False && False)
--     === False
--     *** QED
-- eq_transitivityNatural Zero Zero (Suc _) = trivial
-- eq_transitivityNatural (Suc l) (Suc m) Zero =
--   (eqNatural (Suc l) (Suc m) && eqNatural (Suc m) Zero)
--     === (eqNatural (Suc l) (Suc m) && False)
--     === False
--     *** QED
-- eq_transitivityNatural (Suc l) Zero (Suc n) =
--   (eqNatural (Suc l) Zero && eqNatural Zero (Suc n))
--     === (False && eqNatural Zero (Suc n))
--     === False
--     *** QED
-- eq_transitivityNatural Zero (Suc m) (Suc n) =
--   (eqNatural Zero (Suc m) && eqNatural (Suc m) (Suc n))
--     === (False && eqNatural (Suc m) (Suc n))
--     === False
--     *** QED
-- eq_transitivityNatural (Suc l) (Suc m) (Suc n) = undefined

-- -- ( (eqNatural (Suc l) (Suc m) && eqNatural (Suc m) (Suc n))
-- --     === (eqNatural l m && eqNatural (Suc m) (Suc n))
-- --     === (eqNatural l m && eqNatural m n)
-- --     -- *** Admit
-- --     *** QED
-- -- )
-- --   &&& eq_transitivityNatural l m n

-- {-@
-- equalityNatural :: Equality Natural
-- @-}
-- equalityNatural :: Equality Natural
-- equalityNatural =
--   Equality
--     { eq = eqNatural,
--       eq_reflexivity = eq_reflexivityNatural,
--       eq_symmetry = eq_symmetryNatural,
--       eq_transitivity = eq_transitivityNatural
--     }

{-
# Propositional Equality
-}

{-@
measure eqProp :: a -> a -> Bool
@-}

{-@
type EqProp a X Y = {_:EqualityProp a | eqProp X Y}
@-}

{-@
data EqualityProp :: * -> * where
    LiftEquality :: equality:Equality a -> x:a -> y:a ->
      {_:Proof | eq equality x y} ->
      EqProp a {x} {y}
  | Extensionality :: f:(a -> b) -> g:(a -> b) ->
      (x:a -> EqProp b {f x} {g x}) ->
      EqProp (a -> b) {f x} {g x}
  | Congruency :: x:a -> y:a -> c:(a -> b) ->
      EqProp a {x} {y} ->
      EqProp b {f x} {f y}
@-}
data EqualityProp :: * -> * where
  LiftEquality ::
    Equality a ->
    a ->
    a ->
    Proof ->
    EqualityProp a
  Extensionality ::
    (a -> b) ->
    (a -> b) ->
    (a -> EqualityProp b) ->
    EqualityProp (a -> b)
  Congruency ::
    a ->
    a ->
    (a -> b) ->
    EqualityProp a ->
    EqualityProp b

infixl 3 =~=

-- {-@ (===) :: x:a -> y:{a | } -> {v:a | v = x && v = y} @-}
(=~=) :: a -> a -> a
_ =~= y = y

{-
## Properties
-}

{-
### Has Equality
-}

{-@
class HasEquality a where
  equality :: Equality a
@-}
class HasEquality a where
  equality :: Equality a

{-
### Has Reflexive Propositional Equality
-}

{-@
class HasReflexivity a where
  reflexivity :: x:a -> EqProp a {x} {x}
@-}
class HasReflexivity a where
  reflexivity :: a -> EqualityProp a

instance HasEquality a => HasReflexivity a where
  reflexivity x = LiftEquality equality x x (eq_reflexivity equality x)

-- instance HasReflexivity b => HasReflexivity (a -> b) where
--   reflexivity f = Extensionality f f (\x -> reflexivity (f x))

{-
### Has Symmetric Propositional Equality
-}

-- {-@
-- class HasSymmetry a where
--   symmetry :: x:a -> y:a -> EqProp a {x} {y} -> EqProp {y} {x}
-- @-}
-- class HasSymmetry a where
--   symmetry :: a -> a -> EqualityProp a -> EqualityProp a

-- instance HasEquality a => HasSymmetry a where
--   symmetry x y e = LiftEquality equality y x (eq_symmetry equality x y)
