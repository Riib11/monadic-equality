module Relation.Equality.Prop.Example.Reverse where

import Function
-- import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.Equational
import Relation.Equality.Prop

{-
## Definitions
-}

{-@ reflect append @-}
append :: [a] -> [a] -> [a]
[] `append` ys = ys
(x : xs) `append` ys = x : (xs `append` ys)

{-@ reflect slow @-}
slow :: [a] -> [a]
slow [] = []
slow (x : xs) = slow xs `append` [x]

{-@ reflect bad @-}
bad :: [a] -> [a]
bad xs = xs

{-@ reflect fast @-}
fast :: [a] -> [a]
fast xs = fast_go [] xs

{-@ reflect fast_go @-}
fast_go :: [a] -> [a] -> [a]
fast_go acc [] = acc
fast_go acc (x : xs) = fast_go (x : acc) xs

{-
## Lemmas
-}

{-@ automatic-instances append_assoc @-}
{-@
append_assoc ::
  Eq a =>
  xs:[a] -> ys:[a] -> zs:[a] ->
  {append (append xs ys) zs = append xs (append ys zs)}
@-}
append_assoc :: Eq a => [a] -> [a] -> [a] -> Proof
append_assoc [] ys zs = ()
append_assoc (x : xs) ys zs = append_assoc xs ys zs

{-@ automatic-instances lemma_fast_go_slow @-}
{-@
lemma_fast_go_slow ::
  Eq a =>
  xs:[a] -> ys:[a] ->
  {fast_go ys xs = append (slow xs) ys}
@-}
lemma_fast_go_slow :: Eq a => [a] -> [a] -> Proof
lemma_fast_go_slow [] ys = ()
lemma_fast_go_slow (x : xs) ys =
  lemma_fast_go_slow xs (x : ys)
    ? append_assoc (slow xs) [x] ys

{-@ automatic-instances append_id_right @-}
{-@
append_id_right ::
  Eq a =>
  xs:[a] ->
  {append xs [] = xs}
@-}
append_id_right :: Eq a => [a] -> Proof
append_id_right [] = ()
append_id_right (x : xs) = append_id_right xs

{-
## Theorems
-}

{-@ automatic-instances eq_fast_slow @-}
{-@
eq_fast_slow :: Eq a => xs:[a] -> {fast xs = slow xs}
@-}
eq_fast_slow :: Eq a => [a] -> Proof
eq_fast_slow xs = lemma_fast_go_slow xs [] ? append_id_right (slow xs)

{-@
eqProp_fast_slow :: Eq a => EqualProp ([a] -> [a]) {fast} {slow}
@-}
eqProp_fast_slow :: Eq a => EqualityProp ([a] -> [a])
eqProp_fast_slow =
  Extensionality fast slow $
    \xs -> FromSMT (fast xs) (slow xs) (eq_fast_slow xs)
