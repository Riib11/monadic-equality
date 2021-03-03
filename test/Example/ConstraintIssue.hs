module Example.ConstraintIssue where

{-
TODO: liquid error

/Users/henry/Documents/Projects/monadic-quicksort-verification/monadic-equality/test/Example/ConstraintIssue.hs:3:1: error:
    • Specified type does not refine Haskell type for `Example.ConstraintIssue.R` (Plugged Init types new)
The Liquid type
.
    m##a1Qn -> (forall a##a1Qo .
                (Eq<[]> a##a1Qo) =>
                a##a1Qo -> m##a1Qn a##a1Qo) -> (Example.ConstraintIssue.R m##a1Qn)
.
is inconsistent with the Haskell type
.
    m
-> (forall a. GHC.Classes.Eq a => a -> m a)
-> Example.ConstraintIssue.R m
.
defined at test/Example/ConstraintIssue.hs:3:12-46
.
Specifically, the Liquid component
.
    (GHC.Classes.Eq a##a1Qo)
.
is inconsistent with the Haskell component
.
    a
.

HINT: Use the hole '_' instead of the mismatched component (in the Liquid specification)
    •
  |
3 | data R m = R {r :: forall a. Eq a => a -> m a}
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

-}

data R m = R {r :: forall a. Eq a => a -> m a}
