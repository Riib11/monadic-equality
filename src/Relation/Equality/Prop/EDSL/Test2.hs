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
