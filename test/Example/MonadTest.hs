module Example.MonadTest where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (Monad)

{-
TODO: error

  • Specified type does not refine Haskell type for `Example.MonadTest.Monad` (Plugged Init types new)
The Liquid type

    m ->
    (forall a . a -> m a) ->
    (forall a b . m a -> (a -> m b) -> m b) ->
    (forall a b .
      (Reflexivity<[]> b) =>
      a ->
      (a -> m b) ->
      (Relation.Equality.Prop.EqualityProp m b)) ->
    (Example.MonadTest.Monad m)

is inconsistent with the Haskell type

    m ->
    (forall a. a -> m a) ->
    (forall a b. m a -> (a -> m b) -> m b) ->
    (forall a b.
      Relation.Equality.Prop.Reflexivity b =>
      a ->
      (a -> m b) ->
      Relation.Equality.Prop.EqualityProp (m b)) ->
    Example.MonadTest.Monad m

defined at test/Example/MonadTest.hs:(21,16)-(30,3)

Specifically, the Liquid component

    (Relation.Equality.Prop.Reflexivity b)

is inconsistent with the Haskell component

    a

HINT: Use the hole '_' instead of the mismatched component (in the Liquid specification)

   |
10 | data Monad m = Monad
   |      ^^^^^^

-}

-- TODO: there is an issue using teh `Reflexivity b` typeclass constraint,
-- it causes a liquid type mismatch somehow...

-- {-@
-- data Monad m = Monad
--   { unit :: forall a. a -> m a,
--     bind :: forall a b. m a -> (a -> m b) -> m b,
--     identityLeft ::
--       forall a b.
--       Eq b =>
--       x:a ->
--       k:(a -> m b) ->
--       EqualProp (m b) {bind (unit x) k} {k x}
--   }
-- @-}
-- data Monad m = Monad
--   { unit :: forall a. a -> m a,
--     bind :: forall a b. m a -> (a -> m b) -> m b,
--     identityLeft ::
--       forall a b.
--       Eq b =>
--       a ->
--       (a -> m b) ->
--       EqualityProp (m b)
--   }
