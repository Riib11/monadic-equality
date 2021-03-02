module Example.Context where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop as Prop
import Prelude hiding (flip, map)

-- partially applied functions
{-@
mapEqP ::
  f:(a -> b) -> g:(a -> b) ->
  EqualProp (a -> b) {f} {g} ->
  EqualProp ([a] -> [b]) {map f} {map g}
@-}
mapEqP :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> EqualityProp ([a] -> [b])
mapEqP f g eq = Substitutability f g map eq

{-@
mapEq ::
  f:(a -> b) -> g:(a -> b) ->
  EqualProp (a -> b) {f} {g} ->
  xs:[a] -> EqualProp [b] {map f xs} {map g xs}
@-}
mapEq :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> [a] -> EqualityProp [b]
mapEq f g eq xs =
  Substitutability f g (flipMap xs) eq
    ? fMapEq f xs
    ? fMapEq g xs

{-@
fMapEq :: f:(a -> b) -> xs:[a] -> {map f xs = flipMap xs f}
@-}
fMapEq :: (a -> b) -> [a] -> Proof
fMapEq f xs = trivial ? flipMap xs f

{-@ reflect flipMap @-}
flipMap :: [a] -> (a -> b) -> [b]
flipMap xs f = map f xs

{-@
type Nat = {x:Int | 0 <= x}
@-}

{-@ reflect sucNat @-}
sucNat :: Int -> Int
sucNat x = if 0 <= x then x + 1 else 0

{-@ reflect sucInt @-}
sucInt :: Int -> Int
sucInt x = x + 1

{-@
natDom :: EqualProp (Nat -> Int) {sucInt} {sucNat}
@-}
natDom :: EqualityProp (Int -> Int)
natDom = Extensionality sucInt sucNat $ \x -> FromSMT (sucInt x) (sucNat x) trivial

{-@
client :: xs:[Nat] -> EqualProp [Int] {map sucInt xs} {map sucNat xs}
@-}
client :: [Int] -> EqualityProp [Int]
client = mapEq sucInt sucNat natDom

{-@
clientP :: EqualProp ([Nat] -> [Int]) {map sucInt} {map sucNat}
@-}
clientP :: EqualityProp ([Int] -> [Int])
clientP = mapEqP sucInt sucNat natDom
