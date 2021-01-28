module Relation where

{-
# Relation

A relation is represented by:
- a type `r :: * -> *` which is the type of instances of the relation,
- a function `R :: a -> a -> Bool` which decides the relation.
-}

{-@
data IsRelation r a = IsRelation
  { decide :: (a, a) -> Bool,
    toWitness :: {x:(a, a) | decide x} -> r a,
    fromWitness :: witness:r a -> {x:(a, a) | decide x},
    decide_correct :: {x:(a, a) | decide x} -> {x = fromWitness (toWitness x)}
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
    x :: a,
    y :: a,
    witness :: {_:r a | decide isRelation (x, y)}
   }
@-}
data Relation r a = Relation
  { isRelation :: IsRelation r a,
    relation_x :: a,
    relation_y :: a,
    relation_witness :: r a
  }

-- Type. Abbreviation of "X and Y are related by r".
{-@
type Relates r a X Y =
  {r:Relation r a | X = relation_x r && Y = relation_y r}
@-}

-- Property. A relation is reflexive i.e. R x x.
{-@
type IsReflexive r a =
  x:a ->
  Relates r a {x} {x}
@-}
type IsReflexive r a = a -> r a

-- Property. A relation is symmetric i.e. R x y => R y x.
{-@
type IsSymmetric r a =
  x:a -> y:a ->
  Relates r a {x} {y} ->
  Relates r a {y} {x}
@-}
type IsSymmetric r a = a -> a -> r a -> r a

-- Property. A relation is transitive i.e. R x y => R y z => R x z.
{-@
type IsTransitive r a =
  x:a -> y:a -> z:a ->
  Relates r a {x} {y} ->
  Relates r a {y} {z} ->
  Relates r a {x} {z}
@-}
type IsTransitive r a = a -> a -> a -> r a -> r a -> r a
