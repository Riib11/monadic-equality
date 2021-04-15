module Relation.Equality.Prop.EDSL.Test2 where

import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop

-- {-@
-- measure eqprop :: a -> a -> Bool
-- @-}

-- data EqualityProp a = EqualityProp

-- {-@
-- type EqualProp a X Y = {w:EqualityProp a | eqprop X Y}
-- @-}

-- {-@ assume
-- reflexivity :: x:a -> EqualProp a {x} {x}
-- @-}
-- reflexivity :: a -> EqualityProp a
-- reflexivity x = EqualityProp

-- {-@ assume
-- extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqualProp b {f x} {g x}) -> EqualProp (a -> b) {f} {g}
-- @-}
-- extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
-- extensionality f g pf = EqualityProp

{-@
data Bit = B0 | B1
@-}
data Bit = B0 | B1

{-@
test_int ::
  EqualProp (Int -> Int)
    {identity (\x:Int -> x)}
    {identity (\x:Int -> x)}
@-}
test_int :: EqualityProp (Int -> Int)
test_int =
  extensionality
    (identity (\x -> x))
    (identity (\x -> x))
    (\x -> reflexivity x ? identity (\x -> x) x)

{-
TODO: throws this error when the definition of propositional equality (as
commented out above) is imported rather than included in this file (as it would
be if the code above was not commented.)

/Users/henry/Documents/Projects/monadic-quicksort-verification/monadic-equality/src/Relation/Equality/Prop/EDSL/Test.hs:36:1: error:
    Liquid Type Mismatch
    .
    The inferred type
      VV : {v : (Relation.Equality.Prop.EqualityProp Relation.Equality.Prop.EDSL.Test.Bit -> Relation.Equality.Prop.EDSL.Test.Bit) | eqprop lq_anf$ lq_anf$
                                                                                                                                     && v == Relation.Equality.Prop.extensionality lq_anf$ lq_anf$ lq_anf$}
    .
    is not a subtype of the required type
      VV : {VV : (Relation.Equality.Prop.EqualityProp Relation.Equality.Prop.EDSL.Test.Bit -> Relation.Equality.Prop.EDSL.Test.Bit) | eqprop (Function.identity lam x : Bit . x) (Function.identity lam x : Bit . x)}
    .
   |
36 | test_bit =
   | ^^^^^^^^^^...
Failed, three modules loaded.
-}

{-@
test_bit :: {_:EqualityProp (Bit -> Bit) | eqprop (identity (\x:Bit -> x)) (identity (\x:Bit -> x))}
@-}
test_bit :: EqualityProp (Bit -> Bit)
test_bit =
  extensionality
    (identity (\x -> x))
    (identity (\x -> x))
    (\x -> reflexivity x ? identity (\x -> x) x)

{-@ reflect identity @-}
identity :: a -> a
identity a = a
