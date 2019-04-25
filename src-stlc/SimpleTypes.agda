-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, May/June 2018

-- 1. A universe of simple types; contexts and order-preserving embeddings

-- 1a. Simple types and contexts and their interpretation

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Library

-- We parametrize our universe of types by a set of base types and their interpretation.

module SimpleTypes (Base : Set) (B⦅_⦆ : Base → Set) where

-- Simple types over a set of base types

data Ty : Set where
  base : (b : Base) → Ty
  _⇒_ _×̂_ : (U T : Ty) → Ty

infixr 4 _⇒_
infixr 6 _×̂_

-- Typing contexts

data Cxt : Set where
  ε : Cxt
  _▷_ : (Γ : Cxt) (U : Ty) → Cxt

-- Order-preserving embeddings (OPEs)

data _≤_ : (Γ Δ : Cxt) → Set where
  id≤  : ∀{Γ} → Γ ≤ Γ
  weak : ∀{Γ Δ U} (τ : Γ ≤ Δ) → (Γ ▷ U) ≤ Δ
  lift : ∀{Γ Δ U} (τ : Γ ≤ Δ) → (Γ ▷ U) ≤ (Δ ▷ U)

-- Composition of OPEs: Makes the category of contexts and OPEs.

_∙_ : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → Φ ≤ Γ
τ      ∙ id≤ = τ
τ      ∙ weak τ′ = weak (τ ∙ τ′)
id≤    ∙ lift τ′ = lift τ′
weak τ ∙ lift τ′ = weak (τ ∙ τ′)
lift τ ∙ lift τ′ = lift (τ ∙ τ′)

-- The empty context is the terminal object.

≤ε : ∀ Γ → Γ ≤ ε
≤ε ε        = id≤
≤ε (Γ ▷ U)  = weak (≤ε Γ)

-- Interpretation of types and contexts.

T⦅_⦆ : Ty → Set
T⦅ base b ⦆ = B⦅ b ⦆
T⦅ U ⇒ T ⦆ = T⦅ U ⦆ → T⦅ T ⦆
T⦅ U ×̂ T ⦆ = T⦅ U ⦆ × T⦅ T ⦆

C⦅_⦆ : Cxt → Set
C⦅ ε ⦆ = ⊤
C⦅ Γ ▷ U ⦆ = C⦅ Γ ⦆ × T⦅ U ⦆

Fun : (Γ : Cxt) (T : Ty) → Set
Fun Γ T = C⦅ Γ ⦆ → T⦅ T ⦆

CFun : (Δ Γ : Cxt) → Set
CFun Δ Γ = C⦅ Δ ⦆ → C⦅ Γ ⦆

-- Interpretation of OPE as projections
-- (called "arity functor" in Jung/Tiuryn TLCA 1993).

R⦅_⦆ : ∀{Γ Δ} (τ : Δ ≤ Γ) → C⦅ Δ ⦆ → C⦅ Γ ⦆
R⦅ id≤    ⦆ = id
R⦅ weak τ ⦆ = R⦅ τ ⦆ ∘ proj₁
R⦅ lift τ ⦆ = R⦅ τ ⦆ ×̇′ id

-- The second functor law for R⦅_⦆

ar-comp : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → R⦅ τ ∙ τ′ ⦆ ≡ R⦅ τ ⦆ ∘′ R⦅ τ′ ⦆
ar-comp τ        id≤      = refl
ar-comp τ        (weak τ′) rewrite ar-comp τ τ′ = refl
ar-comp id≤      (lift τ′) = refl
ar-comp (weak τ) (lift τ′) rewrite ar-comp τ τ′ = refl
ar-comp (lift τ) (lift τ′) rewrite ar-comp τ τ′ = refl

{-# REWRITE ar-comp #-}

-- 1b. Kripke predicate basics

-- Kripke predicate over the world of contexts and OPEs.

KPred : (A : Set) → Set₁
KPred A = (Γ : Cxt) (f : C⦅ Γ ⦆ → A) → Set

-- Statement of monotonicity of a Kripke predicate.

Mon : ∀{A} → KPred A → Set
Mon {A} P = ∀{Γ Δ : Cxt} (τ : Δ ≤ Γ) {f : C⦅ Γ ⦆ → A}
  → (⟦f⟧ : P Γ f)
  → P Δ (f ∘′ R⦅ τ ⦆)
