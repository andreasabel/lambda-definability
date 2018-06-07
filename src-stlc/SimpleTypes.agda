-- Simple types and contexts and their interpretation
-- Kripke predicate basics

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Library

module SimpleTypes (Base : Set) (B⦅_⦆ : Base → Set) where

-- Simple types over a set of base types

data Ty : Set where
  base : (b : Base) → Ty
  _⇒_ : (U T : Ty) → Ty

-- Typing contexts

data Cxt : Set where
  ε : Cxt
  _▷_ : (Γ : Cxt) (U : Ty) → Cxt

-- Order-preserving embeddings

data _≤_ : (Γ Δ : Cxt) → Set where
  id≤  : ∀{Γ} → Γ ≤ Γ
  weak : ∀{Γ Δ U} (τ : Γ ≤ Δ) → (Γ ▷ U) ≤ Δ
  lift : ∀{Γ Δ U} (τ : Γ ≤ Δ) → (Γ ▷ U) ≤ (Δ ▷ U)

_∙_ : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → Φ ≤ Γ
τ      ∙ id≤ = τ
τ      ∙ weak τ′ = weak (τ ∙ τ′)
id≤    ∙ lift τ′ = lift τ′
weak τ ∙ lift τ′ = weak (τ ∙ τ′)
lift τ ∙ lift τ′ = lift (τ ∙ τ′)

≤ε : ∀ Γ → Γ ≤ ε
≤ε ε        = id≤
≤ε (Γ ▷ U)  = weak (≤ε Γ)

-- Interpretation of types

T⦅_⦆ : Ty → Set
T⦅ base b ⦆ = B⦅ b ⦆
T⦅ U ⇒ T ⦆ = T⦅ U ⦆ → T⦅ T ⦆

C⦅_⦆ : Cxt → Set
C⦅ ε ⦆ = ⊤
C⦅ Γ ▷ U ⦆ = C⦅ Γ ⦆ × T⦅ U ⦆

Fun : (Γ : Cxt) (T : Ty) → Set
Fun Γ T = C⦅ Γ ⦆ → T⦅ T ⦆

CFun : (Δ Γ : Cxt) → Set
CFun Δ Γ = C⦅ Δ ⦆ → C⦅ Γ ⦆

-- Arity functors: interpretation of OPE as functions

Mor : ∀{Γ Δ} (τ : Δ ≤ Γ) → Set
Mor {Γ} {Δ} τ = C⦅ Δ ⦆ → C⦅ Γ ⦆

R⦅_⦆ : ∀{Γ Δ} (τ : Δ ≤ Γ) → Mor τ
R⦅ id≤    ⦆ = id
R⦅ weak τ ⦆ = R⦅ τ ⦆ ∘ proj₁
R⦅ lift τ ⦆ = R⦅ τ ⦆ ×̇ id

-- The second functor law for R⦅_⦆

ar-comp : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → R⦅ τ ∙ τ′ ⦆ ≡ R⦅ τ ⦆ ∘′ R⦅ τ′ ⦆
ar-comp τ        id≤      = refl
ar-comp τ        (weak τ′) rewrite ar-comp τ τ′ = refl
ar-comp id≤      (lift τ′) = refl
ar-comp (weak τ) (lift τ′) rewrite ar-comp τ τ′ = refl
ar-comp (lift τ) (lift τ′) rewrite ar-comp τ τ′ = refl

{-# REWRITE ar-comp #-}

-- Kripke predicate

KPred : (A : Set) → Set₁
KPred A = (Γ : Cxt) (f : C⦅ Γ ⦆ → A) → Set

mon : ∀{A} → KPred A → Set
mon {A} P = ∀{Γ Δ : Cxt} (τ : Δ ≤ Γ) {f : C⦅ Γ ⦆ → A}
  → (⟦f⟧ : P Γ f)
  → P Δ (f ∘′ R⦅ τ ⦆)
