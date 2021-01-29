module Relation where

{-
# Relation

A relation is represented by
- a type `r :: * -> *` which is the type of instances of the relation,
- a function `decide :: a -> a -> Bool` which decides the relation,
- a function `toWitness :: {x:(a, a) | decide x} -> r a` that, given a pair of
  `a`-terms `x` that are `decide`d to be related, yields a corresponding
  witness `r a`-instance of the relation,
- a function `fromWitness :: witness:r a -> {x:(a, a) | decide x}` that, given
  an instance of the `r a` relation, yields a pair of `a`-terms `x` that
  are `decide`d to be related,
such that
- if a pair of `a`-terms `x` is `decide`d to be related, then `x` is the
  pair of `a`-terms yielded via `fromWitness` of the witness `toWitness x`.
-

-}

{-@
data IsRelation r a = IsRelation
  { decide :: (a, a) -> Bool,
    toWitness :: {x:(a, a) | decide x} -> r a,
    fromWitness :: witness:r a -> {x:(a, a) | decide x},
    decide_correct :: {x:(a, a) | decide x} -> {_:() | x = fromWitness (toWitness x)}
  }
@-}
data IsRelation r a = IsRelation
  { decide :: (a, a) -> Bool,
    toWitness :: (a, a) -> r a,
    fromWitness :: r a -> (a, a),
    decide_correct :: (a, a) -> ()
  }

{-@
data Relation r a = Relation
  { isRelation :: IsRelation r a,
    rx :: a,
    ry :: a,
    rw :: {_:r a | decide isRelation (rx, ry)}
   }
@-}
data Relation r a = Relation
  { isRelation :: IsRelation r a,
    rx :: a,
    ry :: a,
    rw :: r a
  }

-- Type. Abbreviation of "X and Y are related by r".
{-@
type Relates r a X Y =
  {rel:Relation r a | X = rx rel && Y = ry rel}
@-}
-- type Relates r a = Relation r a

{-
# Properties
-}

-- Property. A relation is reflexive i.e. R x x.
{-@
type IsReflexive r a =
  x:a ->
  Relates r a {x} {x}
@-}
-- {rel:Relation r a | x = rx rel && x = ry rel}
type IsReflexive r a = a -> Relation r a

-- Property. A relation is symmetric i.e. R x y => R y x.
{-@
type IsSymmetric r a =
  x:a -> y:a ->
  Relates r a {x} {y} ->
  Relates r a {y} {x}
@-}
-- type IsSymmetric r a = a -> a -> Relation r a -> Relation r a

-- Property. A relation is transitive i.e. R x y => R y z => R x z.
{-@
type IsTransitive r a =
  x:a -> y:a -> z:a ->
  Relates r a {x} {y} ->
  Relates r a {y} {z} ->
  Relates r a {x} {z}
@-}
-- type IsTransitive r a =
--   a -> a -> a -> Relation r a -> Relation r a -> Relation r a
