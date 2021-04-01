{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}

module Relation.Equality.Prop.EDSL.Test where

import Control.Applicative
import Control.Monad
import Data.List
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Meta.Parse as MP
import Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import qualified Text.Parsec as P

{-@
test ::
  Equality a =>
  f:(a -> a -> a) ->
  x:a -> x':a -> EqualProp a {x} {x'} ->
  y:a -> y':a -> EqualProp a {y} {y'} ->
  EqualProp a {f x y} {f x' y'}
@-}
test :: Equality a => (a -> a -> a) -> a -> a -> EqualityProp a -> a -> a -> EqualityProp a -> EqualityProp a
test f x x exx' y y' eyy' =
  [eqpropchain|
    f x y 
    %eqprop
    f x y' %by  
      %rewrite x %-> x' %by 
      exx'
    %eqprop
    f x' y' %by
      %rewrite y %-> y' %by 
      eyy'
    %eqprop
    f x' y' 
      %by 
      %reflexivity
    f x' y'
      %by %symmetry %by
      %reflexivity
  |]
test =
  [eqpropchain|

  |]
