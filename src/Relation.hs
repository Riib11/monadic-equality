module Relation where

{-
Decidable Relation

A decidable relation is represented by:
- a type `r :: * -> *` which is the type of instances of the relation,
- a function `R :: a -> a -> Bool` which decides the relation.
-}

{-@
data Relation r a = Relation
  { decide :: (a, a) -> Bool,
    toWitness :: x:(a, a) -> {rx:() | decide x} -> r a,
    fromWitness :: witness:r a -> {x:(a, a) | decide x},
    decide_correct :: x:a -> {rx:() | decide x} -> {_:() | x = fromWitness (toWitness x rx)}
  }
@-}
data Relation r a = Relation
  { decide :: (a, a) -> Bool,
    toWitness :: (a, a) -> () -> r a,
    fromWitness :: r a -> (a, a),
    decide_correct :: a -> () -> ()
  }

-- Type. Abbreviation of "r a is inhabited and R x y"
{-@ type Relates r a R X Y = {_:r a | R X Y} @-}

-- Property. A relation is reflexive i.e. R x x.
{-@
type IsReflexive r a R =
  x:a ->
  Relates r a {R} {x} {x}
@-}
type IsReflexive r a = a -> r a

-- Property. A relation is symmetric i.e. R x y => R y x.
{-@
type IsSymmetric r a R =
  x:a -> y:a ->
  Relates r a {R} {x} {y} ->
  Relates r a {R} {y} {x}
@-}
type IsSymmetric r a = a -> a -> r a -> r a

-- Property. A relation is transitive i.e. R x y => R y z => R x z.
{-@
type IsTransitive r a R =
  x:a -> y:a -> z:a ->
  Relates r a {R} {x} {y} ->
  Relates r a {R} {y} {z} ->
  Relates r a {R} {x} {z}
@-}
type IsTransitive r a = a -> a -> a -> r a -> r a -> r a
