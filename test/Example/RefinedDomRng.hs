module Example.RefinedDomRng where

import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop as Prop

-- equality over restricted domains and ranges

{-@ reflect sucNat @-}
sucNat :: Int -> Int
sucNat x = if 0 <= x then x + 1 else 0

{-@ reflect sucInt @-}
sucInt :: Int -> Int
sucInt x = x + 1

{-@
type Nat = {x:Int | 0 <= x}
@-}

-- sucInt and sucNat are equal when restricted to the Nat domain
{-@
natDom :: EqualProp (Nat -> Int) {sucInt} {sucNat}
@-}
natDom :: EqualityProp (Int -> Int)
natDom = Extensionality sucInt sucNat $ \x -> FromSMT (sucInt x) (sucNat x) trivial

-- sucInt and sucNat are equal when restricted to the Nat range
{-@
natRng :: EqualProp (Nat -> Nat) {sucInt} {sucNat}
@-}
natRng :: EqualityProp (Int -> Int)
natRng = Extensionality sucInt sucNat $ \x -> FromSMT (sucInt x) (sucNat x) trivial

-- properties of range that depend on inputs

{-@
type SNat X = {v:Nat | v = X + 1}
@-}

-- TODO: why does `trivial` fail?
-- {-@ automatic-instances depRng @-}
-- {-@
-- depRng :: EqualProp (x:Nat -> SNat {x}) {sucInt} {sucNat}
-- @-}
-- depRng :: EqualityProp (Int -> Int)
-- depRng = Extensionality sucInt sucNat $ \x ->
--   FromSMT (sucInt x) (sucNat x) trivial

{-@ fail badDom @-}
{-@
badDom :: EqualProp (Int -> Int) {sucInt} {sucNat}
@-}
badDom :: EqualityProp (Int -> Int)
badDom = Extensionality sucInt sucNat $ \x -> FromSMT (sucInt x) (sucNat x) trivial

{-@ fail badRng @-}
{-@
badRng :: EqualProp (Nat -> {v:Int | v < 0}) {sucInt} {sucNat}
@-}
badRng :: EqualityProp (Int -> Int)
badRng = Extensionality sucInt sucNat $ \x -> FromSMT (sucInt x) (sucNat x) trivial

{-@ fail badDepRng @-}
{-@
badDepRng :: EqualProp (x:Nat -> {v:Int | v = x + 2}) {sucInt} {sucNat}
@-}
badDepRng :: EqualityProp (Int -> Int)
badDepRng = Extensionality sucInt sucNat $ \x -> FromSMT (sucInt x) (sucNat x) trivial
