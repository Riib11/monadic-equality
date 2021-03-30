{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Function.Properties where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Relation.Equality.Prop.Reasoning

{-@
test ::
  Transitivity (b -> c) =>
  f : (a -> b -> c) -> x:a ->
  g : (a -> b -> c) -> y:a ->
  EqualProp (a -> b -> c) {f} {g} ->
  EqualProp a {x} {y} ->
  EqualProp (b -> c) {f x} {g y}
@-}
test ::
  Transitivity (b -> c) =>
  (a -> b -> c) ->
  a ->
  (a -> b -> c) ->
  a ->
  EqualityProp (a -> b -> c) ->
  EqualityProp a ->
  EqualityProp (b -> c)
test f x g y efg exy =
  $( transitivity_chain
       [ [|(f x, substitutability f x y exy)|],
         [|(f y, substitutability (given y) f g efg ? given y f ? given y g)|]
       ]
       [|g y|]
   )
