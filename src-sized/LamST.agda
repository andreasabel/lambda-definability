module LamST where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (Σ ; ∃ ; Σ-syntax ; ∃-syntax ; _×_ ; _,_)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl; module ≡-Reasoning)

open import LamST.Size
open import LamST.Type


v0 : Si∞ (Δ ∷ n)
v0 = var∞ zero

v1 : Si∞ (Δ ∷ n ∷ m)
v1 = var∞ (suc zero)


closeTy : Ty (Δ ∷ ∞) → Ty Δ
closeTy (ℕ n) = ℕ ∞
closeTy (T ⇒ U) = closeTy T ⇒ closeTy U
closeTy (Π n , T) = {!!}


data TV (Δ : SC) : (Γ : TC Δ) (T : Ty Δ) → Set where


data Tm : (Δ : SC) (Γ : TC Δ) (T : Ty Δ) → Set where
  var
    : (x : TV Δ Γ T)
    → Tm Δ Γ T
  Λ_,_
    : (T : Ty Δ)
    → {U : Ty Δ} (t : Tm Δ (Γ ∷ T) U)
    → Tm Δ Γ (T ⇒ U)
  _·_
    : (t : Tm Δ Γ (T ⇒ U))
    → (u : Tm Δ Γ T)
    → Tm Δ Γ U
  Λₛ_,_
    : (n : Si∞ Δ)
    → {T : Ty (Δ ∷ n)} (t : Tm (Δ ∷ n) (wkTC Γ) T)
    → Tm Δ Γ (Π n , T)
  _·ₛ_
    : (t : Tm Δ Γ (Π n , T))
    → {i : Si Δ}
    → (i<n : i <∞ n)
    → Tm Δ Γ (subTy (extendS i<n) T)
  _·∞
    : (t : Tm Δ Γ (Π ∞ , T))
    → Tm Δ Γ (closeTy T)
  zero
    : Tm Δ Γ (Π ∞ , ℕ n)
  suc
    : Tm Δ Γ (Π ∞ , Π v0 , ℕ v0 ⇒ ℕ v1)
  caseℕ[_] : (T : Ty Δ)
    → Tm Δ Γ
        (Π ∞ , wkTy T ⇒ (Π v0 , ℕ v0 ⇒ wkTy (wkTy T))
          ⇒ ℕ v0 ⇒ wkTy T)
  fix[_] : (T : Ty (Δ ∷ ∞))
    → Tm Δ Γ ((Π ∞ , (Π v0 , wkTy T) ⇒ T) ⇒ (Π ∞ , T))


-- one : ∀ {Δ Γ} → Tm Δ Γ (ℕ ∞)
-- one = cast {!!} {!!} ((cast {!refl!} {!sub-∷!} (suc ·ₛ ∞)) ·ₛ {!!}) · {!!}
