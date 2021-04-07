module Relation.Equality.PropI where

import Data.Kind
import Language.Haskell.Liquid.ProofCombinators

data EqPropSing a

{-@
measure eqprop :: EqPropSing a -> a -> a -> Bool
@-}

{-@
type EqProp S X Y = {_:Proof | eqprop S X Y}
@-}

{-@ assume
reflexivity ::
  sing:EqPropSing a ->
  x:a ->
  y:a ->
  EqProp {sing} {x} {y}
@-}
reflexivity ::
  EqPropSing a ->
  a ->
  a ->
  Proof
reflexivity _ _ _ = ()

{-@ assume
extensionality ::
  sing_b:EqPropSing b ->
  sing_a_to_b:EqPropSing (a -> b) ->
  f:(a -> b) ->
  g:(a -> b) ->
  (x:a -> EqProp {sing_b} {f x} {g x}) ->
  EqProp {sing_a_to_b} {f} {g}
@-}
extensionality ::
  EqPropSing b ->
  EqPropSing (a -> b) ->
  (a -> b) ->
  (a -> b) ->
  (a -> Proof) ->
  Proof
extensionality _ _ _ _ _ = ()

{-@ assume
substitutability ::
  sing_a:EqPropSing a ->
  sing_b:EqPropSing b ->
  f:(a -> b) ->
  x:a ->
  y:a ->
  EqProp {sing_a} {x} {y} ->
  EqProp {sing_b} {f x} {f y}
@-}
substitutability ::
  EqPropSing a ->
  EqPropSing b ->
  (a -> b) ->
  a ->
  a ->
  Proof ->
  Proof
substitutability _ _ _ _ _ _ = ()
