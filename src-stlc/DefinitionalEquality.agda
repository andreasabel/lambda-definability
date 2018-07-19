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
wk τ₁ w[ τ₂ ]ˢ = wk (τ₁ ∙ τ₂)
ext σ u w[ τ ]ˢ = ext (σ w[ τ ]ˢ) (u w[ τ ]ᵉ)

-- Lifting a substitution

lifts : ∀{Γ Δ U} (σ : Sub Δ Γ) → Sub (Δ ▷ U) (Γ ▷ U)
lifts σ = ext (σ w[ weak id≤ ]ˢ) (var vz)

-- Executing a substitution

_s[_]ᵛ : ∀{Γ Δ T} (x : Var T Γ) (σ : Sub Δ Γ) → Tm Δ T
x s[ wk τ ]ᵛ = var (x w[ τ ]ᵛ)
vz s[ ext σ u ]ᵛ = u
vs x s[ ext σ u ]ᵛ = x s[ σ ]ᵛ

_s[_]ᵉ : ∀{Γ Δ T} (t : Tm Γ T) (σ : Sub Δ Γ) → Tm Δ T
con c s[ σ ]ᵉ = con c
var x s[ σ ]ᵉ = x s[ σ ]ᵛ
abs t s[ σ ]ᵉ = abs (t s[ lifts σ ]ᵉ)
app t₁ t₂ s[ σ ]ᵉ = app (t₁ s[ σ ]ᵉ) (t₂ s[ σ ]ᵉ)
pair t₁ t₂ s[ σ ]ᵉ = pair (t₁ s[ σ ]ᵉ) (t₂ s[ σ ]ᵉ)
fst t s[ σ ]ᵉ = fst (t s[ σ ]ᵉ)
snd t s[ σ ]ᵉ = snd (t s[ σ ]ᵉ)
zero     s[ σ ]ᵉ = zero
suc t   s[ σ ]ᵉ = suc (t s[ σ ]ᵉ)
recN z s n s[ σ ]ᵉ = recN (z s[ σ ]ᵉ) (s s[ σ ]ᵉ) (n s[ σ ]ᵉ)

-- Single substitution

sg : ∀{Γ U} (u : Tm Γ U) → Sub Γ (Γ ▷ U)
sg u = ext (wk id≤) u

-- Evaluating a substitution

S⦅_⦆ : ∀{Γ Δ} (σ : Sub Δ Γ) → C⦅ Δ ⦆ → C⦅ Γ ⦆
S⦅ wk τ ⦆ = R⦅ τ ⦆
S⦅ ext σ u ⦆ = < S⦅ σ ⦆ , E⦅ u ⦆ >
-- Weakening the evaluation

-- Substitution theorem for evaluation

wk-evals : ∀{Γ Γ' Δ} (σ : Sub Γ Γ') (τ : Δ ≤ Γ) → S⦅ σ w[ τ ]ˢ ⦆ ≡ S⦅ σ ⦆ ∘′ R⦅ τ ⦆
wk-evals (wk τ₁) τ₂ = refl
wk-evals (ext σ u) τ rewrite wk-evals σ τ = refl

-- Evaluation of a term t instantiated by σ
-- is the evaluation of t postcomposed with the action of σ.

sub-evalv : ∀{Γ Δ T} (x : Var T Γ) (σ : Sub Δ Γ) → E⦅ x s[ σ ]ᵛ ⦆ ≡ V⦅ x ⦆ ∘′ S⦅ σ ⦆
sub-evalv x (wk τ) = wk-evalv x τ
sub-evalv vz (ext σ u) = refl
sub-evalv (vs x) (ext σ u) = sub-evalv x σ

sub-eval : ∀{Γ Δ T} (t : Tm Γ T) (σ : Sub Δ Γ) → E⦅ t s[ σ ]ᵉ ⦆ ≡ E⦅ t ⦆ ∘′ S⦅ σ ⦆
sub-eval (con c) σ = refl
sub-eval (var x) σ = sub-evalv x σ
-- why doesn't 'rewrite wk-evals σ (weak id<)' do the trick here?
sub-eval (abs t) σ rewrite sub-eval t (lifts σ) = cong (λ p → (λ x y → E⦅ t ⦆ (p (x , y) , y))) (wk-evals σ (weak id≤))
sub-eval (app t t₁) σ rewrite sub-eval t σ | sub-eval t₁ σ = refl
sub-eval (pair t t₁) σ rewrite sub-eval t σ | sub-eval t₁ σ = refl
sub-eval (fst t) σ rewrite sub-eval t σ = refl
sub-eval (snd t) σ rewrite sub-eval t σ = refl
sub-eval zero σ = refl
sub-eval (suc t) σ rewrite sub-eval t σ = refl
sub-eval (recN z s n) σ rewrite sub-eval z σ | sub-eval s σ | sub-eval n σ = refl

{-# REWRITE sub-eval #-}

-- Definitional equality

data _≡ᵈᵉᶠ_ {Γ} : ∀{T} (t₁ t₂ : Tm Γ T) → Set where
  β : ∀{U T} (t : Tm (Γ ▷ U) T) (u : Tm Γ U) → (app (abs t) u) ≡ᵈᵉᶠ (t s[ sg u ]ᵉ)
  η : ∀{U T} (t : Tm Γ (U ⇒ T)) → (abs (app (t w[ weak id≤ ]ᵉ) (var vz))) ≡ᵈᵉᶠ t
  rec-zero : ∀{T} {z : Tm Γ T} {s : Tm Γ (N ⇒ (T ⇒ T))} {n : Tm Γ N}
                  → n ≡ᵈᵉᶠ zero → (recN z s n) ≡ᵈᵉᶠ z
  rec-suc : ∀{T} {z r : Tm Γ T} {s : Tm Γ (N ⇒ (T ⇒ T))} {n n' : Tm Γ N}
                 → n ≡ᵈᵉᶠ suc n' → (recN z s n') ≡ᵈᵉᶠ r → (recN z s n) ≡ᵈᵉᶠ (app (app s n') r)

  compat-con : ∀ {c : Const } → con c ≡ᵈᵉᶠ con c
  compat-var : ∀{T} (x : Var T Γ) → var x ≡ᵈᵉᶠ var x
  compat-abs : ∀{U T} {t t' : Tm (Γ ▷ U) T} → t ≡ᵈᵉᶠ t' → (abs t) ≡ᵈᵉᶠ (abs t')
  compat-app : ∀{U T} {t t' : Tm Γ (U ⇒ T)} {u u' : Tm Γ U} → t ≡ᵈᵉᶠ t' → u ≡ᵈᵉᶠ u' → (app t u) ≡ᵈᵉᶠ (app t' u')
  compat-pair : ∀{U T} {t t' : Tm Γ T} {u u' : Tm Γ U} → t ≡ᵈᵉᶠ t' → u ≡ᵈᵉᶠ u' → (pair t u) ≡ᵈᵉᶠ (pair t' u')
  compat-fst : ∀{U T} {t t' : Tm Γ (U ×̂ T)} → t ≡ᵈᵉᶠ t' → (fst t) ≡ᵈᵉᶠ (fst t')
  compat-snd : ∀{U T} {t t' : Tm Γ (U ×̂ T)} → t ≡ᵈᵉᶠ t' → (snd t) ≡ᵈᵉᶠ (snd t')
  compat-rec : ∀{T} {z z' : Tm Γ T} {s s' : Tm Γ (N ⇒ (T ⇒ T))} {n n' : Tm Γ N}
                    → z ≡ᵈᵉᶠ z' → s ≡ᵈᵉᶠ s' → n ≡ᵈᵉᶠ n' → (recN z s n) ≡ᵈᵉᶠ (recN z' s' n')


eq-sound : ∀{Γ T} {t₁ t₂ : Tm Γ T} (eq : t₁ ≡ᵈᵉᶠ t₂) → E⦅ t₁ ⦆ ≡ E⦅ t₂ ⦆
eq-sound (β t u) = refl
eq-sound (η {U} {T} t) = refl
eq-sound compat-con = refl
eq-sound (compat-var x) = refl
eq-sound (compat-abs x) rewrite eq-sound x = refl
eq-sound (compat-app x x₁) rewrite eq-sound x | eq-sound x₁ = refl
eq-sound (compat-pair x x₁) rewrite eq-sound x | eq-sound x₁ = refl
-- eq-sound (compat-fst x) = cong (proj₁ ∘_) (eq-sound x)
eq-sound (compat-fst x) rewrite eq-sound x = refl
eq-sound (compat-snd x) rewrite eq-sound x = refl
eq-sound (compat-rec x₁ x₂ x₃) rewrite eq-sound x₁ | eq-sound x₂ | eq-sound x₃ = refl
eq-sound (rec-zero x) rewrite eq-sound x = refl

-- Manual workaround for limitations in Agda's rewrite:
-- (rewrite eq-sound x₂ does not abstract)
eq-sound (rec-suc {T} {z} {r} {s} {n} {n'} x₁ x₂ ) = aux (eq-sound x₁) (eq-sound x₂)
  where
    aux : ∀ {⦅n⦆ ⦅r⦆}
          (eq  : ⦅n⦆             ≡ E⦅ suc n' ⦆)
          (eq' : E⦅ recN z s n' ⦆ ≡ ⦅r⦆      )
          → (λ γ → rec (E⦅ z ⦆ γ) (E⦅ s ⦆ γ) (⦅n⦆ γ)) ≡ (λ γ → E⦅ s ⦆ γ (E⦅ n' ⦆ γ) (⦅r⦆ γ))
    aux refl refl = refl

-- ALT: use funExt
-- eq-sound (rec-suc {T} {z} {r} {s} {n} {n'} x₁ x₂ ) rewrite eq-sound x₁ =
--   funExt λ x → cong (λ z → E⦅ s ⦆ x (E⦅ n' ⦆ x) (z x)) (eq-sound x₂)

-- -}
-- -}
-- -}
-- -}
-- -}
