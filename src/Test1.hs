module Test1 where

type Proof = ()

{-@
type IsReflexive a R = x:a -> {_:Proof | R x x}
@-}
type IsReflexive a = a -> Proof

{-@
type IsSymmetric a R = x:a -> y:a -> {_:Proof | R x y => R y x}
@-}
type IsSymmetric a = a -> a -> Proof

{-@
type IsTransitive a R = x:a -> y:a -> z:a -> {_:Proof | (R x y && R y z) => R x z}
@-}
type IsTransitive a = a -> a -> a -> Proof

{-@
data Equality a = Equality
  { eq :: a -> a -> Bool,
    isReflexive :: IsReflexive a {eq},
    isSymmetric :: IsSymmetric a {eq},
    isTransitive :: IsTransitive a {eq}
   }
@-}
data Equality a = Equality
  { eq :: a -> a -> Bool,
    isReflexive :: IsReflexive a,
    isSymmetric :: IsSymmetric a,
    isTransitive :: IsTransitive a
  }

{-
# SMT Equality

TODO: description
-}

{-@
type EqSMT a X Y = {_:EqualSMT a | X = Y}
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

{-
# Propositional Equality

TODO: description
-}

{-@ measure eqProp :: a -> a -> Bool @-}

{-@
type EqProp a X Y = {_:EqualProp a | eqProp X Y}
@-}

{-@
data EqualProp :: * -> * where
    FromSMT ::
      x:a -> y:a ->
      EqSMT a {x} {y} ->
      EqProp a {x} {y}
  | Extensionality ::
      f:(a -> b) -> g:(a -> b) ->
      (x:a -> EqProp b {f x} {g y}) ->
      EqProp (a -> b) {f} {y}
@-}
data EqualProp :: * -> * where
  FromSMT ::
    a ->
    a ->
    EqualSMT a ->
    EqualProp a
  Extensionality ::
    (a -> b) ->
    (a -> b) ->
    (a -> EqualProp b) ->
    EqualProp (a -> b)
