-- (Meta-level) functions and their characterization by Kripke predicates

{-# OPTIONS --postfix-projections #-}

open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

-- Application (S-combinator)

apply : ∀{A B C : Set} (f : C → A → B) (d : C → A) → C → B
apply f a = λ c → f c (a c)

-- Kripke application

kapp : ∀{A B C D : Set} (f : C → A → B) (τ : D → C) (a : D → A) → D → B
kapp f τ a = λ d → f (τ d) (a d)

-- Kripke predicate

KPred : (A : Set) → Set₁
KPred A = (Γ : Cxt) (f : C⦅ Γ ⦆ → A) → Set

mon : ∀{A} → KPred A → Set
mon {A} P = ∀{Γ Δ : Cxt} (E : Ext Γ Δ) (τ : Mor E) {f : C⦅ Γ ⦆ → A}
  → (⟦f⟧ : P Γ f)
  → P Δ (f ∘′ τ)

-- A Kripke logical predicate is uniquely determined by its definition at base type

record STLC-KLP : Set₁ where
  constructor stlc-klp
  field
    B⟦_⟧  : (b : Base) → KPred B⦅ b ⦆
    monB  : (b : Base) → mon B⟦ b ⟧

-- Kripke logical predicate over the world of context extensions

module STLC-KLP-Ext (P : STLC-KLP) (open STLC-KLP P) where
-- module STLC-KLR (B⟦_⟧ : (b : Base) → KPred B⦅ b ⦆) (monB : ∀ b → mon B⟦ b ⟧) where
-- module KLR (B⟦_⟧ : (b : Base) (Γ : Cxt) (f : C⦅ Γ ⦆ → B⦅ b ⦆) → Set) where

  T⟦_⟧ : (T : Ty) → KPred T⦅ T ⦆
  T⟦ base b ⟧ = B⟦ b ⟧
  T⟦ U ⇒ T ⟧ Γ f =
    ∀{Δ} (E : Ext Γ Δ) (τ : Mor E) (d : Fun Δ U)
    →  (⟦d⟧ : T⟦ U ⟧ Δ d)
    →  T⟦ T ⟧ Δ (kapp f τ d)

  monT : ∀ T → mon T⟦ T ⟧
  monT (base b) = monB b
  monT (U ⇒ T) {Γ} {Δ} Γ⊂Δ τ {f} ⟦f⟧ {Φ} Δ⊂Φ τ′ d ⟦d⟧ = ⟦f⟧ (Γ⊂Δ ∙ Δ⊂Φ) (τ ∘′ τ′) d ⟦d⟧

-- A function is STLC-definable if it satisfies all STLC-KLPs.
-- This is a "big" proposition.

STLC-definable : ∀{Γ T} (f : Fun Γ T) → Set₁
STLC-definable {Γ} {T} f = ∀ (P : STLC-KLP) (open STLC-KLP-Ext P) → T⟦ T ⟧ Γ f

-- STLC

data Var (T : Ty) : (Γ : Cxt) → Set where
  vz : ∀{Γ} → Var T (Γ ▷ T)
  vs : ∀{Γ U} (x : Var T Γ) → Var T (Γ ▷ U)

data Tm (Γ : Cxt) : (T : Ty) → Set where
  var : ∀{T}   (x : Var T Γ) → Tm Γ T
  abs : ∀{U T} (t : Tm (Γ ▷ U) T) → Tm Γ (U ⇒ T)
  app : ∀{U T} (t : Tm Γ (U ⇒ T)) (u : Tm Γ U) → Tm Γ T

-- Weakening

_w[_]ᵛ : ∀{Γ Δ T} (x : Var T Γ) (E : Ext Γ Δ) → Var T Δ
x w[ []    ]ᵛ  =  x
x w[ U ∷ E ]ᵛ  =  (vs x) w[ E ]ᵛ

_w[_]ᵉ : ∀{Γ Δ T} (t : Tm Γ T) (E : Ext Γ Δ) → Tm Δ T
var x   w[ E ]ᵉ = var (x w[ E ]ᵛ)
abs t   w[ E ]ᵉ = abs (t w[ {!!} ]ᵉ)  -- Not definable, need OPEs -- ?0 : Ext (.Γ ▷ .U) (.Δ ▷ .U)
app t u w[ E ]ᵉ = {!!}

-- Evaluation of variables and expressions

V⦅_⦆ : ∀{Γ T} → Var T Γ → Fun Γ T
V⦅ vz ⦆   = proj₂
V⦅ vs x ⦆ = V⦅ x ⦆ ∘′ proj₁

E⦅_⦆ : ∀{Γ T} → Tm Γ T → Fun Γ T
E⦅ var x ⦆   = V⦅ x ⦆
E⦅ abs t ⦆   = curry E⦅ t ⦆
E⦅ app t u ⦆ = apply E⦅ t ⦆ E⦅ u ⦆

-- A syntactic logical relation

TmKLP : STLC-KLP
TmKLP .STLC-KLP.B⟦_⟧ b  Γ f = ∃ λ (t : Tm Γ (base b)) → E⦅ t ⦆ ≡ f
TmKLP .STLC-KLP.monB b {Γ} {Δ} E τ {f} (t , ⦅t⦆≡f) = {!!}
