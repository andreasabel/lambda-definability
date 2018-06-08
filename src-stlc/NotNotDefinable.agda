-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, May/June 2018

-- 4a. Using Kripke predicates to refute STLC-definability of boolean negation.

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Data.Bool.Base
open import Library

import SimpleTypes
import STLCDefinable

module NotNotDefinable where

-- We consider STLC with a base type "bool" that is inhabited by
-- two constants "true" and "false".

data Base : Set where
  bool : Base

B⦅_⦆ : Base → Set
B⦅ bool ⦆ = Bool

open SimpleTypes Base B⦅_⦆

data Const : Set where
  true  : Const
  false : Const

ty : Const → Ty
ty true  = base bool
ty false = base bool

c⦅_⦆ : (c : Const) → T⦅ ty c ⦆
c⦅ true ⦆ = true
c⦅ false ⦆ = false

-- We now prove that negation is not STLC definable
-- by constructing a countermodel.

open STLCDefinable Base B⦅_⦆ Const ty c⦅_⦆

-- We define the predicate to be "constant or a projection".
--
-- To be a projection is to be the image of a variable under evaluation.
-- This seems to be the most economic definition.
-- A direct definition by induction on the context would look very similar.

data IsConstantOrProjection Γ T (f : Fun Γ T) : Set where
  isConstant   : (eq : ∀ γ γ' → f γ ≡ f γ')      → IsConstantOrProjection Γ T f
  isProjection : (x : Var T Γ) (eq : f ≡ V⦅ x ⦆) → IsConstantOrProjection Γ T f

-- Negation is neither constant nor a projection from the singleton context (x:bool).

not′ : Fun (ε ▷ base bool) (base bool)
not′ = not ∘′ proj₂

notNotConstantOrProjection : IsConstantOrProjection (ε ▷ base bool) (base bool) not′ → ⊥
notNotConstantOrProjection (isConstant eq)      = case eq (_ , true) (_ , false) of λ()
notNotConstantOrProjection (isProjection vz eq) = case cong (λ z → z (_ , true)) eq of λ()
notNotConstantOrProjection (isProjection (STLCDefinable.vs ()) eq)

-- "Being constant or a projection" is a valid Kripke logical predicate at base type.
-- This amounts to show monotonicity, i.e., closure under composition with projections τ.

NN-Base : STLC-KLP-Base
NN-Base .STLCDefinable.STLC-KLP-Base.B⟦_⟧ bool Γ f = IsConstantOrProjection Γ _ f
NN-Base .STLCDefinable.STLC-KLP-Base.monB bool τ (isConstant eq) =
  isConstant (λ γ γ' → eq (R⦅ τ ⦆ γ) (R⦅ τ ⦆ γ'))
NN-Base .STLCDefinable.STLC-KLP-Base.monB bool τ (isProjection x refl) =
  isProjection (x w[ τ ]ᵛ) (sym (wk-evalv x τ))

-- The constants true/false satisfy this KLP.
-- (Because they denote constant functions.)

NN : STLC-KLP
NN .STLCDefinable.STLC-KLP.klp-base = NN-Base
NN .STLCDefinable.STLC-KLP.satC true  = isConstant (λ _ _ → refl)
NN .STLCDefinable.STLC-KLP.satC false = isConstant (λ _ _ → refl)

-- Since negation is not modelled by this predicate, it cannot be STLC-definable.

thm : STLC-definable (ε ▷ base bool) (base bool) not′ → ⊥
thm def = notNotConstantOrProjection (def NN)

-- Q.E.D.
