module Equality where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)


--
-- Relation
--

record Relation (R : Set → Set) (A : Set) : Set where
  field
    relate : A × A → Bool
    to-witness : ∀ x → relate x ≡ true → R A
    from-witness : R A → ∃[ x ] (relate x ≡ true)
    to-from-witness : ∀ x d → x ≡ (proj₁ ∘ from-witness) (to-witness x d)

  Related : A × A → Set
  Related (x , y) = R A × relate (x , y) ≡ true


-- Properties

IsReflexive : ∀ R A (rel : Relation R A) → Set
IsReflexive R A rel = ∀ x → Related (x , x)
  where open Relation rel

IsSymmetric : ∀ R A (rel : Relation R A) → Set
IsSymmetric R A rel = ∀ x y → Related (x , y) → Related (y , x)
  where open Relation rel

IsTransitive : ∀ R A (rel : Relation R A) → Set
IsTransitive R A rel = ∀ x y z → Related (x , y) → Related (y , z) → Related (x , z)
  where open Relation rel


--
-- Equality
--

record Equality (E : Set → Set) (A : Set) : Set where
  field
    rel : Relation E A
    isReflexive  : IsReflexive  E A rel
    isSymmetric  : IsSymmetric  E A rel
    isTransitive : IsTransitive E A rel


--
-- SMT Equality
--

postulate
  -- datatype
  EqualitySMT : ∀ A → A → A → Set

  -- instances
  equalitySMT-Bool : Equality EqualitySMT Bool
  equalitySMT-ℕ    : Equality EqualitySMT ℕ

  -- eq-smt : (A : Set) (x y : A) → Bool


--
-- Propositional Equality
--

postulate
  eq-prop : ∀ (A : Set) (x y : A) → Bool
    

data EqualityProp : ∀ A → A → A → Set where
  injection-SMT :
    ∀ (A : Set) (equ : Equality EqualitySMT A) x y →
      Relation.Related EqualitySMT (x , y) →
      Relation.Related EqualityProp (x , y)
  -- extensional :
  --   ∀ (A B : Set) f g →
  --     (∀ x → EqualityProp 
      
