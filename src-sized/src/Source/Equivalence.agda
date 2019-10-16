-- Equality of terms up to sizes.
{-# OPTIONS --without-K --safe #-}
module Source.Equivalence where

open import Source.Size hiding (x ; y ; z ; Ctx)
open import Source.Term
open import Source.Type
open import Util.Prelude


infix 4 _≈_ _≈T_


data _≈T_ {Δ Ω} : (T : Type Δ) (U : Type Ω) → Set where
  Nat
    : Nat n ≈T Nat m
  Stream
    : Stream n ≈T Stream m
  Arr
    : T ≈T T′
    → U ≈T U′
    → (T ⇒ T′) ≈T (U ⇒ U′)
  All
    : T ≈T T′
    → (Π n , T) ≈T (Π m , T′)


data _≈Γ_ {Δ Ω} : (Γ : Ctx Δ) (Ψ : Ctx Ω) → Set where
  []
    : [] ≈Γ []
  Snoc
    : Γ ≈Γ Ψ
    → T ≈T U
    → (Γ ∙ T) ≈Γ (Ψ ∙ U)


data _≈_ {Δ Ω} : (t : Term Δ) (u : Term Ω) → Set where
  var
    : var x ≈ var x
  lam
    : T ≈T U
    → t ≈ u
    → Λ T , t ≈ Λ U , u
  app
    : t ≈ t′
    → u ≈ u′
    → t · u ≈ t′ · u′
  lamₛ
    : t ≈ u
    → Λₛ n , t ≈ Λₛ m , u
  appₛ
    : t ≈ u
    → t ·ₛ n ≈ u ·ₛ m
  zero
    : zero n ≈ zero m
  suc
    : i ≈ i′
    → suc n m i ≈ suc n′ m′ i′
  cons
    : i ≈ i′
    → is ≈ is′
    → cons i n is ≈ cons i′ n′ is′
  head
    : is ≈ is′
    → head n is ≈ head n′ is′
  tail
    : is ≈ is′
    → tail n is m ≈ tail n′ is′ m′
  caseNat
    : T ≈T T′
    → i ≈ i′
    → z ≈ z′
    → s ≈ s′
    → caseNat T n i z s ≈ caseNat T′ n′ i′ z′ s′
  fix
    : T ≈T T′
    → t ≈ t′
    → fix T t n ≈ fix T′ t′ n′


SizeIrrelevanceExampleStatement : Set
SizeIrrelevanceExampleStatement
  = ∀ {Δ t n m}
  → Δ , [] ⊢ t ∶ Π ∞ , Nat v0
  → t ·ₛ n ≈ t ·ₛ m
