module Example.Reverse where

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

{-@ reflect reverse_slow @-}
reverse_slow :: [a] -> [a]
reverse_slow [] = []
reverse_slow (x : xs) = reverse_slow xs `append` [x]

{-@ reflect reverse_bad @-}
reverse_bad :: [a] -> [a]
reverse_bad xs = xs

{-@ reflect reverse_fast @-}
reverse_fast :: [a] -> [a]
reverse_fast xs = reverse_fast_go [] xs

{-@ reflect reverse_fast_go @-}
reverse_fast_go :: [a] -> [a] -> [a]
reverse_fast_go acc [] = acc
reverse_fast_go acc (x : xs) = reverse_fast_go (x : acc) xs

{-
## Lemmas
-}

{-@ automatic-instances append_assoc @-}
{-@
append_assoc ::
  xs:[a] -> ys:[a] -> zs:[a] ->
  {append (append xs ys) zs = append xs (append ys zs)}
@-}
append_assoc :: [a] -> [a] -> [a] -> Proof
append_assoc [] ys zs = ()
append_assoc (x : xs) ys zs = append_assoc xs ys zs

{-@ automatic-instances reverse_fast_go_slow_lemma @-}
{-@
reverse_fast_go_slow_lemma ::
  xs:[a] -> ys:[a] ->
  {reverse_fast_go ys xs = append (reverse_slow xs) ys}
@-}
reverse_fast_go_slow_lemma :: [a] -> [a] -> Proof
reverse_fast_go_slow_lemma [] ys = ()
reverse_fast_go_slow_lemma (x : xs) ys =
  reverse_fast_go_slow_lemma xs (x : ys)
    ? append_assoc (reverse_slow xs) [x] ys

{-@ automatic-instances append_id_right @-}
{-@
append_id_right ::
  xs:[a] ->
  {append xs [] = xs}
@-}
append_id_right :: [a] -> Proof
append_id_right [] = ()
append_id_right (x : xs) = append_id_right xs
