module Relation.Equality.Prop.ExtensionalityBad where

import Function
import Language.Haskell.Liquid.ProofCombinators

-- TODO: TESTING

{-@ assume
funext :: f:(a -> b) -> g:(a -> b) -> (x:a -> {f x = g x}) -> {f = g}
@-}
funext :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof
funext _ _ _ = ()

{-@ reflect h @-}
h :: Int -> Int
h x = x

{-@ reflect k @-}
k :: Int -> Int
k x = 1

{-@
lemma :: x:Int -> {True}
@-}
lemma :: Int -> Proof
lemma _ = ()

{-@
thm :: {h = k}
@-}
thm :: Proof
thm = funext h k lemma

{-@
ex :: {h 2 = k 2}
@-}
ex :: Proof
ex = thm
