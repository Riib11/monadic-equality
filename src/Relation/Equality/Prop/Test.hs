module Relation.Equality.Prop.Test where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (map)

-- TODO: TESTING

{-@ reflect h @-}
h :: Int -> Int
h x = x

{-@ reflect k @-}
k :: Int -> Int
k x = x

-- {-@ assume
-- lemma :: x:Int -> EqualProp Int {h x} {k x}
-- @-}
-- lemma :: Int -> EqualityProp Int
-- lemma x = EqualityProp ? h x ? k x

-- SAFE

{-@
e_h_k :: EqualProp (Int -> Int) {h} {k}
@-}
e_h_k :: EqualityProp (Int -> Int)
e_h_k = extensionality h k (\x -> reflexivity (h x) ? k x)

{-@
e_mh_mk :: EqualProp ([Int] -> [Int]) {map h} {map k}
@-}
e_mh_mk :: EqualityProp ([Int] -> [Int])
e_mh_mk = reflexivity (map h) ? map k ? e_h_k

{-@
e_mhx_mkx :: xs:[Int] -> EqualProp [Int] {map h xs} {map k xs}
@-}
e_mhx_mkx :: [Int] -> EqualityProp [Int]
e_mhx_mkx xs = reflexivity (map h xs) ? map k xs ? e_h_k

-- UNSAFE

-- not equal to k
{-@ reflect f @-}
f :: Int -> Int
f x = x + 1

{-@ fail e_f_k @-}
{-@
e_f_k :: EqualProp (Int -> Int) {f} {k}
@-}
e_f_k :: EqualityProp (Int -> Int)
e_f_k = extensionality f k (\x -> reflexivity (f x) ? k x)

-- {-@ fail e_mf_mk @-}
-- {-@
-- e_mf_mk :: EqualProp ([Int] -> [Int]) {map f} {map k}
-- @-}
-- e_mf_mk :: EqualityProp ([Int] -> [Int])
-- e_mf_mk = reflexivity (map f) ? map k ? e_f_k

-- {-@ fail e_mfx_mkx @-}
-- {-@
-- e_mfx_mkx :: xs:[Int] -> EqualProp [Int] {map f xs} {map k xs}
-- @-}
-- e_mfx_mkx :: [Int] -> EqualityProp [Int]
-- e_mfx_mkx xs = reflexivity (map f xs) ? map k xs ? e_f_k

-- -- SAFE
-- {-@
-- thm ::
--   f:(a -> b) ->
--   g:(a -> b) ->
--   EqualProp (a -> b) {f} {g} ->
--   l:[a] ->
--   EqualProp [b] {map f l} {map g l}
-- @-}
-- thm :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> [a] -> EqualityProp [b]
-- thm f g efg l =
--   reflexivity (map f l)
--     ? map f
--     ? map g
--     ? map f l
--     ? map g l
