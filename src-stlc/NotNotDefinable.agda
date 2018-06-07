-- Negation is not STLC-definable

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Data.Bool.Base

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)

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

-- IsConstant : ∀{Γ T} (f : Fun Γ T) → Set
-- IsConstant f = ∀ γ γ' → f γ ≡ f γ'

-- IsProjection : ∀{Γ T} (f : Fun Γ T) → Set
-- IsProjection {Γ} {T} f = ∃ λ (x : Var T Γ) → f ≡ V⦅ x ⦆

data IsConstantOrProjection Γ T (f : Fun Γ T) : Set where
  isConstant : (eq : ∀ γ γ' → f γ ≡ f γ') → IsConstantOrProjection Γ T f
  isProjection :  (x : Var T Γ) (eq : f ≡ V⦅ x ⦆) → IsConstantOrProjection Γ T f

-- Negation is neither constant nor a projection from the singleton context (x:bool).

not′ : Fun (ε ▷ base bool) (base bool)
not′ = not ∘′ proj₂

notNotConstantOrProjection : IsConstantOrProjection (ε ▷ base bool) (base bool) not′ → ⊥
notNotConstantOrProjection (isConstant eq)      with eq (_ , true) (_ , false)
... | ()
notNotConstantOrProjection (isProjection vz eq) with cong (λ z → z (_ , true)) eq
... | ()
notNotConstantOrProjection (isProjection (STLCDefinable.vs ()) eq)

-- "Being constant or a projection" is a valid Kripke logical predicate at base type.
-- This amounts to show monotonicity, i.e., closure under composition with projections τ.

NN-Base : STLC-KLP-Base
STLCDefinable.STLC-KLP-Base.B⟦ NN-Base ⟧ bool Γ f = IsConstantOrProjection Γ _ f
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
