-- (Meta-level) functions and their characterization by Kripke predicates

open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Function using (id; _∘_; _∘′_)

module Fun (Base : Set) (B⦅_⦆ : Base → Set) where

-- Simple types over a set of base types

data Ty : Set where
  base : (b : Base) → Ty
  _⇒_ : (U T : Ty) → Ty

-- Typing contexts

data Cxt : Set where
  ε : Cxt
  _▷_ : (Γ : Cxt) (U : Ty) → Cxt

-- Context extensions

data Ext (Γ : Cxt) : Cxt → Set where
  []  : Ext Γ Γ
  _∷_ : ∀{Δ} (U : Ty) (E : Ext (Γ ▷ U) Δ) → Ext Γ Δ

_∙_ : ∀{Γ Δ Φ} (E : Ext Γ Δ) (E′ : Ext Δ Φ) → Ext Γ Φ
[] ∙ E′ = E′
(U ∷ E) ∙ E′ = U ∷ (E ∙ E′)

-- Interpretation of types

T⦅_⦆ : Ty → Set
T⦅ base b ⦆ = B⦅ b ⦆
T⦅ U ⇒ T ⦆ = T⦅ U ⦆ → T⦅ T ⦆

C⦅_⦆ : Cxt → Set
C⦅ ε ⦆ = ⊤
C⦅ Γ ▷ U ⦆ = C⦅ Γ ⦆ × T⦅ U ⦆

Fun : (Γ : Cxt) (T : Ty) → Set
Fun Γ T = C⦅ Γ ⦆ → T⦅ T ⦆

Mor : ∀{Γ Δ} (E : Ext Γ Δ) → Set
Mor {Γ} {Δ} E = C⦅ Δ ⦆ → C⦅ Γ ⦆

-- Kripke application

kapp : ∀{A B C D : Set} (f : C → A → B) (τ : D → C) (a : D → A) → D → B
kapp f τ a = λ d → f (τ d) (a d)

-- Kripke predicate

KPred : (A : Set) → Set₁
KPred A = (Γ : Cxt) (f : C⦅ Γ ⦆ → A) → Set

mon : ∀{A} → KPred A → Set
mon {A} P = ∀{Γ Δ : Cxt} (E : Ext Γ Δ) (τ : Mor E) {f : C⦅ Γ ⦆ → A}
  → P Γ f
  → P Δ (f ∘′ τ)

-- Kripke logical predicate over the world of context extensions

module KLR (B⟦_⟧ : (b : Base) → KPred B⦅ b ⦆) (monB : ∀ b → mon B⟦ b ⟧) where
-- module KLR (B⟦_⟧ : (b : Base) (Γ : Cxt) (f : C⦅ Γ ⦆ → B⦅ b ⦆) → Set) where

  T⟦_⟧ : (T : Ty) → KPred T⦅ T ⦆
  T⟦ base b ⟧ = B⟦ b ⟧
  T⟦ U ⇒ T ⟧ Γ f =
    ∀{Δ} (E : Ext Γ Δ) (τ : C⦅ Δ ⦆ → C⦅ Γ ⦆) (d : C⦅ Δ ⦆ → T⦅ U ⦆)
    →  T⟦ U ⟧ Δ d
    →  T⟦ T ⟧ Δ (kapp f τ d)

  monT : ∀ T → mon T⟦ T ⟧
  monT (base b) = monB b
  monT (U ⇒ T) {Γ} {Δ} Γ⊂Δ τ {f} ⟦f⟧ {Φ} Δ⊂Φ τ′ d ⟦d⟧ = ⟦f⟧ (Γ⊂Δ ∙ Δ⊂Φ) (τ ∘′ τ′) d ⟦d⟧
