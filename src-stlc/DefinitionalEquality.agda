-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, May/June 2018

-- Definitional equality

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Library
import SimpleTypes

-- The notion of Kripke predicate is parametrized by base types
-- and simply-typed constants and their interpretation.

module DefinitionalEquality
  (Base : Set)  (B⦅_⦆ : Base → Set) (open SimpleTypes Base B⦅_⦆)
  (Const : Set) (ty : Const → Ty) (c⦅_⦆ : (c : Const) → T⦅ ty c ⦆)
  where

open import STLCDefinable Base B⦅_⦆ Const ty c⦅_⦆

data Sub (Δ : Cxt) : (Γ : Cxt) → Set where
  wk  : ∀{Γ}   (τ : Δ ≤ Γ) → Sub Δ Γ
  ext : ∀{Γ U} (σ : Sub Δ Γ) (u : Tm Δ U) → Sub Δ (Γ ▷ U)

-- Weakening a substitution

_w[_]ˢ : ∀{Γ Δ Φ} (σ : Sub Δ Γ) (τ : Φ ≤ Δ) → Sub Φ Γ
wk τ′   w[ τ ]ˢ = wk (τ′ ∙ τ)
ext σ u w[ τ ]ˢ = ext (σ w[ τ ]ˢ) (u w[ τ ]ᵉ)

-- Lifting a substitution

lifts : ∀{Γ Δ U} (σ : Sub Δ Γ) → Sub (Δ ▷ U) (Γ ▷ U)
lifts σ = ext (σ w[ weak id≤ ]ˢ) (var vz)

-- Executing a substitution

_s[_]ᵛ : ∀{Γ Δ T} (x : Var T Γ) (σ : Sub Δ Γ) → Tm Δ T
x    s[ wk τ    ]ᵛ = var (x w[ τ ]ᵛ)
vs x s[ ext σ u ]ᵛ = x s[ σ ]ᵛ
vz   s[ ext σ u ]ᵛ = u

_s[_]ᵉ : ∀{Γ Δ T} (t : Tm Γ T) (σ : Sub Δ Γ) → Tm Δ T
con c    s[ σ ]ᵉ = con c
var x    s[ σ ]ᵉ = x s[ σ ]ᵛ
abs t    s[ σ ]ᵉ = abs (t s[ lifts σ ]ᵉ)
app t u  s[ σ ]ᵉ = app (t s[ σ ]ᵉ) (u s[ σ ]ᵉ)
pair u t s[ σ ]ᵉ = pair (u s[ σ ]ᵉ) (t s[ σ ]ᵉ)
fst t    s[ σ ]ᵉ = fst (t s[ σ ]ᵉ)
snd t    s[ σ ]ᵉ = snd (t s[ σ ]ᵉ)

-- Single substitution

sg : ∀{Γ U} (u : Tm Γ U) → Sub Γ (Γ ▷ U)
sg u = ext (wk id≤) u

-- Evaluating a substitution

S⦅_⦆ : ∀{Γ Δ} (σ : Sub Δ Γ) → C⦅ Δ ⦆ → C⦅ Γ ⦆
S⦅ wk τ ⦆    = R⦅ τ ⦆
S⦅ ext σ u ⦆ = < S⦅ σ ⦆ , E⦅ u ⦆ >

-- Weakening the evaluation

-- Substitution theorem for evaluation

wk-evals : ∀{Γ Γ' Δ} (σ : Sub Γ Γ') (τ : Δ ≤ Γ) → S⦅ σ w[ τ ]ˢ ⦆ ≡ S⦅ σ ⦆ ∘′ R⦅ τ ⦆
wk-evals = {!!}

-- Evaluation of a term t instantiated by σ
-- is the evaluation of t postcomposed with the action of σ.

sub-evalv : ∀{Γ Δ T} (x : Var T Γ) (σ : Sub Δ Γ) → E⦅ x s[ σ ]ᵛ ⦆ ≡ V⦅ x ⦆ ∘′ S⦅ σ ⦆
sub-evalv x      (wk τ)  = wk-evalv x τ
sub-evalv vz     (ext σ u) = refl
sub-evalv (vs x) (ext σ u) = sub-evalv x σ

sub-eval : ∀{Γ Δ T} (t : Tm Γ T) (σ : Sub Δ Γ) → E⦅ t s[ σ ]ᵉ ⦆ ≡ E⦅ t ⦆ ∘′ S⦅ σ ⦆
sub-eval (con c)    σ = refl
sub-eval (var x)    σ = sub-evalv x σ
sub-eval (abs t)    σ rewrite sub-eval t (lifts σ) = {!!}
sub-eval (app t u)  σ rewrite sub-eval t σ | sub-eval u σ = refl
sub-eval (pair u t) σ rewrite sub-eval u σ | sub-eval t σ = refl
sub-eval (fst t)    σ with E⦅ t s[ σ ]ᵉ ⦆ | sub-eval t σ
... | .(E⦅ t ⦆ ∘ S⦅ σ ⦆) | refl = refl -- rewrite sub-eval t σ = refl
sub-eval (snd t)    σ = cong (proj₂ ∘_) (sub-eval t σ)

{-# REWRITE sub-eval #-}

-- Definitional equality

data Eq {Γ} : ∀{T} (t₁ t₂ : Tm Γ T) → Set where
  β : ∀{U T} (t : Tm (Γ ▷ U) T) (u : Tm Γ U) → Eq (app (abs t) u) (t s[ sg u ]ᵉ)
  η : ∀{U T} (t : Tm Γ (U ⇒ T)) → Eq (abs (app (t w[ weak id≤ ]ᵉ) (var vz))) t

eq-sound : ∀{Γ T} {t₁ t₂ : Tm Γ T} (eq : Eq t₁ t₂) → E⦅ t₁ ⦆ ≡ E⦅ t₂ ⦆
eq-sound (β t u) = refl
-- eq-sound (η t) = refl
-- C-u C-u C-c C-,
eq-sound (η {U} {T} t) = begin
  E⦅ abs (app (t w[ weak id≤ ]ᵉ) (var vz)) ⦆                      ≡⟨⟩
  curry E⦅ app (t w[ weak id≤ ]ᵉ) (var vz) ⦆                      ≡⟨⟩
  curry (apply E⦅ t w[ weak {U = U} id≤ ]ᵉ ⦆ E⦅ var {T = U} vz ⦆) ≡⟨⟩
  curry (apply (E⦅ t ⦆ ∘ R⦅ weak {U = U} id≤ ⦆) V⦅ vz {T = U} ⦆)  ≡⟨⟩
  curry (apply (E⦅ t ⦆ ∘ R⦅ id≤ ⦆ ∘ proj₁) proj₂)                 ≡⟨⟩
  curry (apply (E⦅ t ⦆ ∘ proj₁) proj₂)                            ≡⟨⟩
  curry (λ p → E⦅ t ⦆ (proj₁ p) (proj₂ p))                        ≡⟨⟩
  E⦅ t ⦆
  ∎ where open ≡-Reasoning


-- -}
-- -}
-- -}
-- -}
-- -}
