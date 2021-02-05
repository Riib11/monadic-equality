module Test4 where

{-
# Proof
-}

type Proof = ()

toProof :: a -> Proof
toProof _ = ()

(&&&) :: Proof -> Proof -> Proof
x &&& _ = x

{-@ withProof :: x:a -> b -> {v:a | v = x} @-}
withProof :: a -> b -> a
withProof x _ = x

{-@ impossible :: {v:a | false} -> b @-}
impossible :: a -> b
impossible _ = undefined

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

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

(&) :: a -> (a -> b) -> b
x & f = f x

{-
# Equality
-}

{-@
measure eq :: a -> a -> Bool
@-}

{-@
class Equality a where
  eq_ :: x:a -> y:a -> {v:Bool | v <=> eq x y}
  reflexivity :: x:a ->
    {_:Proof | eq x x}
  symmetry :: x:a -> y:a ->
    {_:Proof | eq x y} ->
    {_:Proof | eq y x}
  transitivty :: x:a -> y:a -> z:a ->
    {_:Proof | eq x y} ->
    {_:Proof | eq y z} ->
    {_:Proof | eq x z}
@-}
class Equality a where
  eq_ :: a -> a -> Bool
  reflexivity :: a -> Proof
  symmetry :: a -> a -> Proof -> Proof
  transitivty :: a -> a -> a -> Proof -> Proof -> Proof

{-@
assume congruency ::
  x:a -> y:a -> c:(a -> b) ->
  {_:Proof | eq x y} ->
  {_:Proof | eq (c x) (c y)}
@-}
congruency :: Equality a => a -> a -> (a -> b) -> Proof -> Proof
congruency _ _ _ _ = trivial

{-@
assume fromEquality :: x:a -> y:a -> {_:Proof | eq x y} -> {x = y}
@-}
fromEquality :: a -> a -> Proof -> Proof
fromEquality _ _ _ = trivial

{-@
assume toEquality :: x:a -> y:a -> {_:Proof | x = y} -> {eq x y}
@-}
toEquality :: a -> a -> Proof -> Proof
toEquality _ _ _ = trivial

-- {-
-- # Base Equalities
-- -}

-- {-
-- ## Bool Equality
-- -}

{-@
assume eqBool :: x:Bool -> y:Bool -> {v:Bool | v <=> eq x y}
@-}
eqBool :: Bool -> Bool -> Bool
eqBool True True = True
eqBool False False = True
eqBool _ _ = False

{-@ automatic-instances reflexivityBool @-}
{-@
reflexivityBool :: x:a -> {_:Proof | eq x x}
@-}
reflexivityBool :: a -> Proof
reflexivityBool x = toEquality x x e
  where
    {-@
    e :: {x = x}
    @-}
    e :: Proof
    e = trivial

{-@ automatic-instances symmetryBool @-}
{-@
symmetryBool ::
  x:a -> y:a ->
  {_:Proof | eq x y} ->
  {_:Proof | eq y x}
@-}
symmetryBool :: a -> a -> Proof -> Proof
symmetryBool x y exy = toEquality y x eyx
  where
    {-@
    eyx :: {y = x}
    @-}
    eyx :: Proof
    eyx = fromEquality x y exy

{-@ automatic-instances transitivtyBool @-}
{-@
transitivtyBool ::
  x:a -> y:a -> z:a ->
  {_:Proof | eq x y} ->
  {_:Proof | eq y z} ->
  {_:Proof | eq x z}
@-}
transitivtyBool :: a -> a -> a -> Proof -> Proof -> Proof
transitivtyBool x y z exy eyz = toEquality x z exz
  where
    {-@
    exz :: {x = z}
    @-}
    exz :: Proof
    exz = fromEquality x y exy &&& fromEquality y z eyz

instance Equality Bool where
  eq_ = eqBool
  reflexivity = reflexivityBool
  symmetry = symmetryBool
  transitivty = transitivtyBool

-- {-
-- ## Natural Number Equality
-- -}

-- {-@
-- data Natural = Zero | Suc Natural
-- @-}
-- data Natural = Zero | Suc Natural

-- -- {-@
-- -- measure sizeNatural :: Natural -> Int
-- -- @-}
-- -- sizeNatural :: Natural -> Int
-- -- sizeNatural Zero = 0
-- -- sizeNatural (Suc n) = 1 + sizeNatural n

-- {-@ reflect eqNatural @-}
-- eqNatural :: Natural -> Natural -> Bool
-- eqNatural Zero Zero = True
-- eqNatural (Suc m) (Suc n) = eqNatural m n
-- eqNatural _ _ = False

-- {-@ automatic-instances neq_Zero_Suc @-}
-- {-@
-- neq_Zero_Suc :: n:Natural -> {not (eqNatural (Suc n) Zero)}
-- @-}
-- neq_Zero_Suc :: Natural -> Proof
-- neq_Zero_Suc _ = trivial

-- -- {-@ automatic-instances reflexivityNatural @-}
-- -- {-@
-- -- reflexivityNatural :: x:Natural -> {_:Proof | eqNatural x x}
-- -- @-}
-- -- reflexivityNatural :: IsReflexive Natural
-- -- reflexivityNatural Zero = trivial
-- -- reflexivityNatural (Suc n) = reflexivityNatural n

-- -- {-@ automatic-instances symmetryNatural @-}
-- -- {-@
-- -- symmetryNatural :: IsSymmetric Natural {eqNatural}
-- -- @-}
-- -- symmetryNatural :: IsSymmetric Natural
-- -- symmetryNatural Zero Zero = trivial
-- -- symmetryNatural (Suc _) Zero = trivial
-- -- symmetryNatural Zero (Suc _) = trivial
-- -- symmetryNatural (Suc m) (Suc n) = symmetryNatural m n

-- -- {-@
-- -- transitivtyNatural :: IsTransitive Natural {eqNatural}
-- -- @-}
-- -- transitivtyNatural :: IsTransitive Natural
-- -- transitivtyNatural Zero Zero Zero = trivial
-- -- transitivtyNatural (Suc _) Zero Zero = trivial
-- -- transitivtyNatural Zero (Suc m) Zero =
-- --   (eqNatural Zero (Suc m) && eqNatural (Suc m) Zero)
-- --     === (False && False)
-- --     === False
-- --     *** QED
-- -- transitivtyNatural Zero Zero (Suc _) = trivial
-- -- transitivtyNatural (Suc l) (Suc m) Zero =
-- --   (eqNatural (Suc l) (Suc m) && eqNatural (Suc m) Zero)
-- --     === (eqNatural (Suc l) (Suc m) && False)
-- --     === False
-- --     *** QED
-- -- transitivtyNatural (Suc l) Zero (Suc n) =
-- --   (eqNatural (Suc l) Zero && eqNatural Zero (Suc n))
-- --     === (False && eqNatural Zero (Suc n))
-- --     === False
-- --     *** QED
-- -- transitivtyNatural Zero (Suc m) (Suc n) =
-- --   (eqNatural Zero (Suc m) && eqNatural (Suc m) (Suc n))
-- --     === (False && eqNatural (Suc m) (Suc n))
-- --     === False
-- --     *** QED
-- -- transitivtyNatural (Suc l) (Suc m) (Suc n) = undefined

-- -- -- ( (eqNatural (Suc l) (Suc m) && eqNatural (Suc m) (Suc n))
-- -- --     === (eqNatural l m && eqNatural (Suc m) (Suc n))
-- -- --     === (eqNatural l m && eqNatural m n)
-- -- --     -- *** Admit
-- -- --     *** QED
-- -- -- )
-- -- --   &&& transitivtyNatural l m n

-- -- {-@
-- -- equalityNatural :: Equality Natural
-- -- @-}
-- -- equalityNatural :: Equality Natural
-- -- equalityNatural =
-- --   Equality
-- --     { eq = eqNatural,
-- --       reflexivity = reflexivityNatural,
-- --       symmetry = symmetryNatural,
-- --       transitivty = transitivtyNatural
-- --     }

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
    FromEquality :: Equality a => x:a -> y:a ->
      {_:Proof | eq x y} ->
      EqProp a {x} {y}
  | Extensionality :: f:(a -> b) -> g:(a -> b) ->
      (x:a -> EqProp b {f x} {g x}) ->
      EqProp (a -> b) {f x} {g x}
  | Congruency :: x:a -> y:a -> c:(a -> b) ->
      EqProp a {x} {y} ->
      EqProp b {f x} {f y}
@-}
data EqualityProp :: * -> * where
  FromEquality ::
    Equality a =>
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
### Completeness of Propositional Equality (w.r.t SMT Equality)
-}

-- TODO: implement
{-@
assume toEqualitySMT :: Equality a => x:a -> y:a -> EqProp a {x} {y} -> {x = y}
@-}
toEqualitySMT :: Equality a => a -> a -> EqualityProp a -> Proof
toEqualitySMT _ _ _ = trivial

-- TODO: prove toEqualitySMT is inverse of FromEquality

{-
### Reflexive Propositional Equality
-}

{-@
class ReflexivityProp a where
  reflexivityProp ::
    x:a ->
    EqProp a {x} {x}
@-}
class ReflexivityProp a where
  reflexivityProp ::
    a ->
    EqualityProp a

instance Equality a => ReflexivityProp a where
  reflexivityProp x = FromEquality x x (reflexivity x)

-- TODO: doesn't recognize eqProp x x
-- instance ReflexivityProp b => ReflexivityProp (a -> b) where
--   reflexivityProp f = Extensionality f f e'
--     where
--       e' x = reflexivityProp (f x)

{-
### Symmetric Propositional Equality
-}

{-@
class SymmetryProp a where
  symmetryProp ::
    x:a -> y:a ->
    EqProp a {x} {y} ->
    EqProp a {y} {x}
@-}
class SymmetryProp a where
  symmetryProp ::
    a -> a -> EqualityProp a -> EqualityProp a

instance Equality a => SymmetryProp a where
  symmetryProp x y e = FromEquality y x e'
    where
      e' = symmetry x y (toEquality x y (toProof (toEqualitySMT x y e)))

-- TODO: doesn't derive any eqProp from use of symmetryProp
-- instance SymmetryProp b => SymmetryProp (a -> b) where
--   symmetryProp f g e = Extensionality f g e'
--     where
--       e' x =
--         symmetryProp
--           (f x)
--           (g x)
--           (symmetryProp (f x) (g x) (Congruency f g (x &) e))

{-
### Transitive Propositional Equality
-}

{-@
class TransitiveProp a where
  transitivtyProp ::
    x:a -> y:a -> z:a ->
    EqProp a {x} {y} ->
    EqProp a {y} {z} ->
    EqProp a {x} {z}
@-}
class TransitiveProp a where
  transitivtyProp ::
    a -> a -> a -> EqualityProp a -> EqualityProp a -> EqualityProp a

instance Equality a => TransitiveProp a where
  transitivtyProp x y z exy eyz = FromEquality x z e'
    where
      e' = toEquality x z (toEqualitySMT x y exy &&& toEqualitySMT y z eyz)

-- TODO: doesn't derive any eqProp from use of transitivityProp
-- instance TransitiveProp b => TransitiveProp (a -> b) where
--   transitivtyProp f g h efg egh = Extensionality f g e'
--     where
--       e' x =
--         transitivtyProp
--           (f x)
--           (g x)
--           (h x)
--           (Congruency f g (x &) efg)
--           (Congruency g h (x &) egh)

{-
### Congruency-preserving Propositional Equality
-}

{-@
class CongruencyProp a b where
  congruencyProp ::
    x:a -> y:a -> c:(a -> b) ->
    EqProp a {x} {y} ->
    EqProp b {c x} {c y}
@-}
class CongruencyProp a b where
  congruencyProp ::
    a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

instance (Equality a, Equality b) => CongruencyProp a b where
  congruencyProp x y c exy =
    FromEquality
      (c x)
      (c y)
      -- {eq (c x) (c y)}
      ( congruency
          x
          y
          c
          -- {eq x y}
          (toEquality x y (toEqualitySMT x y exy))
      )

-- TODO: doesn't derive correct eqProp from use of congruencyProp
-- instance CongruencyProp a c => CongruencyProp a (b -> c) where
--   -- congruencyProp :: a -> a -> (a -> b -> c) -> Proof -> Proof
--   congruencyProp x y c exy = Extensionality (c x) (c y) e'
--     where
--       e' z = congruencyProp x y (\x' -> c x' z) exy
