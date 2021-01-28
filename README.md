# monadic-equality

Formulating equality of
[monadic](https://hackage.haskell.org/package/base-4.14.1.0/docs/Control-Monad.html)
terms in [Liquid Haskell](http://ucsd-progsys.github.io/liquidhaskell/).

## Why Monadic Equality?

Consider the monad laws:

```
       q >> lift = m

     lift x >> k = k x

(q >>= k1) >> k2 = q >>= (k1 >=> k2)
```

where

```
m     :: * -> * where Monad m

x     :: a
q     :: m a
k, k1 :: a -> m b
k2    :: b -> m c
lift  ::
(>>=) :: m a -> (a -> m b) -> m b
(>=>) :: (a -> m b) -> (b -> m c) -> (a -> m c)
```

These laws are equalities between monadic terms. But what kind of quality is it?
Well, if we are using the `Writer String Int = (String, Int)` monadic terms,
then the equality is the equality that the pair type `forall a b. (a, b)`
derives from the equality of `String` and the equality of `Int`.

However, what if we are using the `Reader String Int = String -> Int`?
Generally, the arrow type `forall a b. a -> b` doesn't derive any equality. So
implicitly we must be using some kind of extensionality, since the monad laws
are for _all_ monads, not just the ones with non-extensional equalities.

In Liquid Haskell, extensional equality is not included for two main reasons:

1. The SMT-solver backend for Liquid Haskell does not use quantifiers, so cannot
   represent extensional equality.
2. Liquid Haskell's SMT equality is not type-indexed, and type-unindexed
   extensional equality is unsound.

So, to formulate monadic equality (i.e. equality of monadic terms) in Liquid
Haskell, we need a notion of type-indexed propositional equality in order to
include extensionality, and additionally a notion of monadic equality that
relies on propositional equality and may be either extensional or
non-extensional depending on the monad.

This work may perhaps be extendible to derive a certain kind of equality for
generic typeclasses (of which `Monad` is one example).

## Propositional Equality

TODO

## Monadic Equality

TODO

## Examples

TODO
