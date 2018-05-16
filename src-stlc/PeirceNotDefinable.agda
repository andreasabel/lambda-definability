-- There is no λ-definable function in the Peirce type ((A → B) → A) → A

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Data.Bool.Base

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)

import SimpleTypes
import STLCDefinable

module PeirceNotDefinable where

-- Dependent ⊥-elim

⊥-elim′ : ∀ {a} {A : ⊥ → Set a} (x : ⊥) → A x
⊥-elim′ ()

-- We consider the Peirce formula over two "empty" base types

data Base : Set where
  a b : Base

-- In the set-interpretation, the types are actually not empty.
-- If they were, we would not be able to get the necessary witnesses.

B⦅_⦆ : Base → Set
B⦅ _ ⦆ = ⊤

-- We consider λ-calculus with no constants

open SimpleTypes Base B⦅_⦆
open STLCDefinable Base B⦅_⦆ ⊥ ⊥-elim ⊥-elim′

A = base a
B = base b

-- A counter model to the Peirce type:
-- We interpret A as being-a-projection
-- and B as the empty predicate.

IsProjection : ∀ Γ T (f : Fun Γ T) → Set
IsProjection Γ T f = ∃ λ (x : Var T Γ) → f ≡ V⦅ x ⦆

no-proj-from-ε : ∀ T {f : Fun ε T} (p : IsProjection ε T f) → ⊥
no-proj-from-ε _ (() , _)

NP-Base : STLC-KLP-Base
NP-Base .STLC-KLP-Base.B⟦_⟧ a Γ f = IsProjection Γ A f
NP-Base .STLC-KLP-Base.B⟦_⟧ b Γ f = ⊥  -- b is always empty
NP-Base .STLC-KLP-Base.monB a τ (x , refl) = x w[ τ ]ᵛ ,  sym (wk-evalv x τ)
NP-Base .STLC-KLP-Base.monB b τ ()

NP : STLC-KLP
NP .STLCDefinable.STLC-KLP.klp-base = NP-Base
NP .STLCDefinable.STLC-KLP.satC ()

Peirce = ((A ⇒ B) ⇒ A) ⇒ A

-- Theorem: the Peirce type is not inhabited in STLC

thm : ∀ f → STLC-definable ε Peirce f → ⊥
thm f def = no-proj-from-ε A (def NP id≤ {λ _ → _} (λ τ ⟦d⟧ → lem ⟦d⟧))
  where
  -- Lemma: T⟦ A ⇒ B ⟧ Δ is false.
  open STLC-KLP NP
  lem : ∀ {Δ d} → T⟦ A ⇒ B ⟧ Δ d → ∀{X : Set} → X
  lem {Δ} {d} ⟦d⟧ with (⟦d⟧ (weak id≤) (vz , refl))
  ... | ()

-- The argument runs just like the Kripke countermodel for Peirce in IPL.

-- We can drop the functions like f since we interpeted A and B as ⊤
-- in the set-theoretic interpretation.

-- Proof: Suppose ⟦ Pierce ⟧ ε and derive a contradiction.
-- Since ⟦ A ⟧ ε is false ("no-proj-from-ε A"), it is sufficient to show ⟦ (A → B) → A ⟧ ε.
-- Assume τ : Δ ≤ ε and ⟦ A → B ⟧ Δ.  We show ⟦ A ⟧ Δ by absurdity of ⟦ A → B ⟧ Δ.
-- To this end, note that ⟦ A ⟧ (Δ.A) holds while ⟦ B ⟧ (Δ.A) is false (irrespective of Δ).
-- QED
