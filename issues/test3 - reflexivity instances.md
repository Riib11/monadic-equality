In module `Test3`, we have

```
{-@
newtype Reflexivity a = Reflexivity
  {reflexivity :: x:a -> EqProp a {x} {x}}
@-}
newtype Reflexivity a = Reflexivity
  {reflexivity :: a -> EqualityProp a}

-- base case
{-@
equality_reflexivity_base :: EqualityAxiomatic a -> Reflexivity a
@-}
equality_reflexivity_base :: EqualityAxiomatic a -> Reflexivity a
equality_reflexivity_base iEqualityAxiomatic =
  Reflexivity
    { reflexivity = equality_reflexive_base_aux iEqualityAxiomatic
    }

{-@
equality_reflexive_base_aux :: EqualityAxiomatic a -> x:a -> EqProp a {x} {x}
@-}
equality_reflexive_base_aux :: forall a. EqualityAxiomatic a -> a -> EqualityProp a
equality_reflexive_base_aux iEqualityAxiomatic x =
  Axiomatic iEqualityAxiomatic x x (eqax_reflexivity iEqualityAxiomatic x)

-- inductive step
{-@
equality_reflexivity_induction ::
  Reflexivity b -> Reflexivity (a -> b)
@-}
equality_reflexivity_induction ::
  Reflexivity b -> Reflexivity (a -> b)
equality_reflexivity_induction iReflexivity =
  Reflexivity
    { reflexivity = equality_reflexivity_induction_aux iReflexivity
    }

{-@
equality_reflexivity_induction_aux ::
  Reflexivity b -> (a -> b) -> EqualityProp (a -> b)
@-}
equality_reflexivity_induction_aux ::
  Reflexivity b -> (a -> b) -> EqualityProp (a -> b)
equality_reflexivity_induction_aux iReflexivity f =
  Extensionality f f (\x -> reflexivity iReflexivity (f x))
```

When building, I get this ghc error:

```
❯ stack build
monadic-equality> configure (lib)
Configuring monadic-equality-0.1.0.0...
monadic-equality> build (lib)
Preprocessing library for monadic-equality-0.1.0.0..
Building library for monadic-equality-0.1.0.0..
[11 of 11] Compiling Test3
ghc: panic! (the 'impossible' happened)
  (GHC version 8.10.3:
	Uh oh.
    addC: malformed constraint:
cconsE:
 t = forall a . x:a -> {VV##0 : (Test3.EqualityProp a) | eqprop x x}
 te = lq_tmp$x##798:{lq_tmp$x##794 : a | $k_##789[VV##788:=lq_tmp$x##794][lq_tmp$x##786:=iEqualityAxiomatic##a18j][lq_tmp$x##790:=lq_tmp$x##794]} -> {lq_tmp$x##796 : (Test3.EqualityProp {lq_tmp$x##795 : a | $k_##789[VV##788:=lq_tmp$x##795][lq_tmp$x##783:=lq_tmp$x##796][lq_tmp$x##786:=iEqualityAxiomatic##a18j][lq_tmp$x##787:=lq_tmp$x##798][lq_tmp$x##790:=lq_tmp$x##795]}) | eqprop lq_tmp$x##798 lq_tmp$x##798}lq_anf$##7205759403792804346lq_tmp$x##798:{lq_tmp$x##794 : a | $k_##789[VV##788:=lq_tmp$x##794][lq_tmp$x##786:=iEqualityAxiomatic##a18j][lq_tmp$x##790:=lq_tmp$x##794]} -> {lq_tmp$x##796 : (Test3.EqualityProp {lq_tmp$x##795 : a | $k_##789[VV##788:=lq_tmp$x##795][lq_tmp$x##783:=lq_tmp$x##796][lq_tmp$x##786:=iEqualityAxiomatic##a18j][lq_tmp$x##787:=lq_tmp$x##798][lq_tmp$x##790:=lq_tmp$x##795]}) | eqprop lq_tmp$x##798 lq_tmp$x##798}
 <:
forall a . x:a -> {VV##0 : (Test3.EqualityProp a) | eqprop x x}

Please report this as a GHC bug:  https://www.haskell.org/ghc/reportabug


--  While building package monadic-equality-0.1.0.0 (scroll up to its section to see the error) using:
      /Users/henry/.stack/setup-exe-cache/x86_64-osx/Cabal-simple_mPHDZzAJ_3.2.1.0_ghc-8.10.3 --builddir=.stack-work/dist/x86_64-osx/Cabal-3.2.1.0 build lib:monadic-equality --ghc-options " -fdiagnostics-color=always"
    Process exited with code: ExitFailure 1
```
