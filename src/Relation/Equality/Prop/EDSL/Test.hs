{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Relation.Equality.Prop.EDSL.Test where

import Control.Applicative
import Control.Monad
import Data.List
import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Meta.Parse as MP
import Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import qualified Text.Parsec as P

{-
## V2
-}

{-@
data Bit = B0 | B1
@-}
data Bit = B0 | B1

{-@
test_bit ::
  EqualProp (Bit -> Bit)
    {identity (\x:Bit -> x)}
    {identity (\x:Bit -> x)}
@-}
test_bit :: EqualityProp (Bit -> Bit)
test_bit =
  extensionality
    (identity (\x -> x))
    (identity (\x -> x))
    (\x -> reflexivity x ? identity (\x -> x) x)

{-
## V1

{-@
test ::
  Equality a =>
  f:(a -> a -> a) ->
  x:a -> x':a -> EqualProp a {x} {x'} ->
  y:a -> y':a -> EqualProp a {y} {y'} ->
  EqualProp a {f x y} {f x' y'}
@-}
test :: Equality a => (a -> a -> a) -> a -> a -> EqualityProp a -> a -> a -> EqualityProp a -> EqualityProp a
test f x x' exx' y y' eyy' =
  [eqpropchain|
      f x y
    %eqprop
      f x' y
        %by %rewrite x %to x'
        %by exx'
    %eqprop
      f x' y'
        %by %rewrite y %to y'
        %by eyy'
  |]

-- same as `test`, but with the generated code
{-@
test' ::
  Equality a =>
  f:(a -> a -> a) ->
  x:a -> x':a -> EqualProp a {x} {x'} ->
  y:a -> y':a -> EqualProp a {y} {y'} ->
  EqualProp a {f x y} {f x' y'}
@-}
test' :: Equality a => (a -> a -> a) -> a -> a -> EqualityProp a -> a -> a -> EqualityProp a -> EqualityProp a
test' f x x' exx' y y' eyy' =
  transitivity
    (f x y)
    (f x' y)
    (f x' y')
    ( substitutability
        (apply (\hole_0 -> f hole_0 y))
        x
        x'
        exx'
        ? apply (\hole_0 -> f hole_0 y) x
        ? apply (\hole_0 -> f hole_0 y) x'
    )
    ( substitutability (apply (\hole_1 -> f x' hole_1)) y y' eyy'
        ? apply (\hole_1 -> f x' hole_1) y
        ? apply (\hole_1 -> f x' hole_1) y'
    )
-}
