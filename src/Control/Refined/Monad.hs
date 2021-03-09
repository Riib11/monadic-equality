module Control.Refined.Monad where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (Monad, pure, seq)

{-
# Monad
-}

{-
## Data
-}

{-@
data Monad m = Monad
  { pure :: forall a. a -> m a,
    bind :: forall a b. m a -> (a -> m b) -> m b
  }
@-}
data Monad m = Monad
  { pure :: forall a. a -> m a,
    bind :: forall a b. m a -> (a -> m b) -> m b
  }

{-@
class MonadLaws m where
  bind_identity_left :: forall a b. (Equality a, Equality b) => mnd:Monad m -> x:a -> k:(a -> m b) ->
    (EqualProp (m b) {bind mnd (pure mnd x) k} {k x})
  bind_identity_right :: forall a. (Equality a) => mnd:Monad m -> m:m a ->
    (EqualProp (m a) {bind mnd m (pure mnd)} {m})
  bind_associativity :: forall a b c. (Equality a, Equality b, Equality c) => mnd:Monad m -> m:m a -> k1:(a -> m b) -> k2:(b -> m c) ->
    (EqualProp (m c) {bind mnd (bind mnd m k1) k2} {bind mnd m (kleisli mnd k1 k2)})
@-}
class MonadLaws m where
  bind_identity_left :: forall a b. (Equality a, Equality b) => Monad m -> a -> (a -> m b) -> EqualityProp (m b)
  bind_identity_right :: forall a. (Equality a) => Monad m -> m a -> EqualityProp (m a)
  bind_associativity :: forall a b c. (Equality a, Equality b, Equality c) => Monad m -> m a -> (a -> m b) -> (b -> m c) -> EqualityProp (m c)

{-
TODO: still getting this error... (now confirmed to be a bug)

/Users/henry/Documents/Projects/monadic-quicksort-verification/monadic-equality/src/Control/Refined/Monad.hs:29:25: error:
    • Specified type does not refine Haskell type for `Control.Refined.Monad.bind_identity_left` (Plugged Init types new)
The Liquid type
.
    (Control.Refined.Monad.MonadLaws m) -> forall a b .
                                           (Equality<[]> a, Equality<[]> b) =>
                                           (Control.Refined.Monad.Monad m) -> a -> (a -> m b) -> (Relation.Equality.Prop.EqualityProp m b)
.
is inconsistent with the Haskell type
.
    forall (m :: * -> *) a b.
(Control.Refined.Monad.MonadLaws m,
 Relation.Equality.Prop.Equality a,
 Relation.Equality.Prop.Equality b) =>
Control.Refined.Monad.Monad m
-> a -> (a -> m b) -> Relation.Equality.Prop.EqualityProp (m b)
.
defined at src/Control/Refined/Monad.hs:37:3-112
.
Specifically, the Liquid component
.
    (Relation.Equality.Prop.Equality b)
.
is inconsistent with the Haskell component
.
    a
.

HINT: Use the hole '_' instead of the mismatched component (in the Liquid specification)
    •
   |
29 |   bind_identity_left :: forall a b. (Equality a, Equality b) => mnd:Monad m -> x:a -> k:(a -> m b) ->
   |                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^...
-}

{-
## Utilities
-}

{-@ reflect kleisli @-}
kleisli :: Monad m -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisli mnd k1 k2 x = bind mnd (k1 x) k2

{-@ reflect join @-}
join :: Monad m -> m (m a) -> m a
join mnd mm = bind mnd mm identity

{-@ reflect seq @-}
seq :: Monad m -> m a -> m b -> m b
seq mnd ma mb = bind mnd ma (\_ -> mb)

{-@ reflect map @-}
map :: Monad m -> (a -> b) -> (m a -> m b)
map mnd f m = bind mnd m (\x -> pure mnd (f x))

{-@ reflect map2 @-}
map2 :: Monad m -> (a -> b -> c) -> (m a -> m b -> m c)
map2 mnd f ma mb = bind mnd ma (\x -> bind mnd mb (\y -> pure mnd (f x y)))
