-- Simple types and contexts and their interpretation
-- Kripke predicate basics

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

{-# BUILTIN REWRITE _≡_ #-}

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

-- Application (S-combinator)

apply : ∀{A B C : Set} (f : C → A → B) (d : C → A) → C → B
apply f a = λ c → f c (a c)

-- Kripke application

kapp : ∀{A B C D : Set} (f : C → A → B) (τ : D → C) (a : D → A) → D → B
kapp f τ a = λ d → f (τ d) (a d)

-- Arity functors: interpretation of OPE as functions

_×̇_ : ∀{A B C D : Set} → (A → C) → (B → D) → A × B → C × D
(f ×̇ g) (x , y) = f x , g y

Mor : ∀{Γ Δ} (E : Δ ≤ Γ) → Set
Mor {Γ} {Δ} E = C⦅ Δ ⦆ → C⦅ Γ ⦆

Ar : ∀{Γ Δ} (E : Δ ≤ Γ) → Mor E
Ar id≤ = id
Ar (weak E) = Ar E ∘ proj₁
Ar (lift E) = Ar E ×̇ id

-- The second functor law for Ar

ar-comp : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → Ar (τ ∙ τ′) ≡ Ar τ ∘′ Ar τ′
ar-comp τ id≤      = refl
ar-comp τ (weak τ′) rewrite ar-comp τ τ′ = refl
ar-comp id≤ (lift τ′) = refl
ar-comp (weak τ) (lift τ′) rewrite ar-comp τ τ′ = refl
ar-comp (lift τ) (lift τ′) rewrite ar-comp τ τ′ = refl

{-# REWRITE ar-comp #-}

-- Kripke predicate

KPred : (A : Set) → Set₁
KPred A = (Γ : Cxt) (f : C⦅ Γ ⦆ → A) → Set

mon : ∀{A} → KPred A → Set
mon {A} P = ∀{Γ Δ : Cxt} (τ : Δ ≤ Γ) {f : C⦅ Γ ⦆ → A}
  → (⟦f⟧ : P Γ f)
  → P Δ (f ∘′ Ar τ)
