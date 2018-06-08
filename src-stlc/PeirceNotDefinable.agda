-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, May/June 2018

-- 4. Using Kripke predicates to refute STLC-definability of an inhabitant of Peirce's formula.

-- There is no λ-definable function in the Peirce type ((A → B) → A) → A

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Library
import SimpleTypes
import STLCDefinable

module PeirceNotDefinable where

-- We consider the Peirce formula over two "empty" base types:

data Base : Set where
  a b : Base

-- In the set-interpretation, the types are actually not empty.
-- If they were, we would not be able to get the necessary witnesses.

B⦅_⦆ : Base → Set
B⦅ _ ⦆ = ⊤

-- We consider λ-calculus with no constants

open SimpleTypes   Base B⦅_⦆
open STLCDefinable Base B⦅_⦆ ⊥ ⊥-elim (λ())

A = base a
B = base b

-- A counter model to the Peirce type:
-- We interpret A as being-a-projection
-- and B as the empty predicate.

IsProjection : ∀ Γ T (f : Fun Γ T) → Set
IsProjection Γ T f = ∃ λ (x : Var T Γ) → f ≡ V⦅ x ⦆

NP-Base : STLC-KLP-Base
NP-Base .STLC-KLP-Base.B⟦_⟧ a Γ f = IsProjection Γ A f
NP-Base .STLC-KLP-Base.B⟦_⟧ b Γ f = ⊥  -- b is always empty
NP-Base .STLC-KLP-Base.monB a τ (x , refl) = x w[ τ ]ᵛ , sym (wk-evalv x τ)
NP-Base .STLC-KLP-Base.monB b τ ()

NP : STLC-KLP
NP .STLCDefinable.STLC-KLP.klp-base = NP-Base
NP .STLCDefinable.STLC-KLP.satC ()

Peirce = ((A ⇒ B) ⇒ A) ⇒ A

-- Lemma: Cannot project anything from the empty context.

no-proj-from-ε : ∀ T {f : Fun ε T} (p : IsProjection ε T f) → ⊥
no-proj-from-ε _ (() , _)

-- Theorem: the Peirce type is not inhabited in STLC.

-- The argument runs just like the Kripke countermodel for Peirce in IPL.

-- We can drop the functions like f since we interpeted A and B as ⊤
-- in the set-theoretic interpretation.

-- Proof: Suppose ⟦ Pierce ⟧ ε and derive a contradiction.
-- Since ⟦ A ⟧ ε is false ("no-proj-from-ε A"), it is sufficient to show ⟦ (A → B) → A ⟧ ε.
-- Assume τ : Δ ≤ ε and ⟦ A → B ⟧ Δ.  We show ⟦ A ⟧ Δ by absurdity of ⟦ A → B ⟧ Δ ("lemma").
-- To this end, note that ⟦ A ⟧ (Δ.A) holds while ⟦ B ⟧ (Δ.A) is false (irrespective of Δ).

thm : ∀ f → STLC-definable ε Peirce f → ⊥
thm f def = no-proj-from-ε A (def NP id≤ (λ τ ⟦d⟧ → lemma ⟦d⟧))
  where
  open STLC-KLP NP

  -- Lemma: T⟦ A ⇒ B ⟧ Δ is always false.
  lemma : ∀ {Δ d} → T⟦ A ⇒ B ⟧ Δ d → ∀{X : Set} → X
  lemma ⟦d⟧ = case ⟦d⟧ (weak id≤) (vz , refl) of λ()

-- Q.E.D.
