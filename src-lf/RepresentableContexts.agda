
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Level using (Lift)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product as Prod using (Σ; ∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import Types

module RepresentableContexts
  (TyC : Set) (Ind : TyC → Set) (F⦅_⦆ : (k : TyC) → Ind k → Set) (open Univ TyC Ind F⦅_⦆)
  (Const : Set) (ty : Const → Ty ε) (c⦅_⦆ : (c : Const) → T⦅ ty c ⦆ _) (open Constants Const ty c⦅_⦆)
  where

open import Terms TyC Ind F⦅_⦆ Const ty c⦅_⦆ hiding (Var; V⦅_⦆)

mutual
  data RC : Set where
    ε : RC
    _▻_ : (Γ : RC) (A : Ty (ElC Γ)) → RC

  ElC : RC → Cxt
  ElC ε = ε
  ElC (Γ ▻ A) = ElC Γ ▷ T⦅ A ⦆

RMor : (Δ Γ : RC) → Set
RMor Δ Γ = Mor (ElC Δ) (ElC Γ)


-- Variables

data Var : (Γ : RC) (A : Ty (ElC Γ)) → Set₁ where
  vz : ∀{Γ} A                 → Var (Γ ▻ A) (A [ weak id≤ ]T)
  vs : ∀{Γ} A B (x : Var Γ A) → Var (Γ ▻ B) (A [ weak id≤ ]T)

-- Evaluating variables

V⦅_⦆ : ∀{Γ T} → Var Γ T → Fun (ElC Γ) T
V⦅ vz _     ⦆ = proj₂
V⦅ vs _ _ x ⦆ = V⦅ x ⦆ ∘ proj₁


module Fund (P : LF-KLP) (open LF-KLP P) where

  -- Extension of KLP to contexts
  -- NEED representable contexts

  -- Unfortunately, this does not work:
  -- open WeakKripke P
  -- {-# REWRITE wk-KLP #-}
  -- ERROR:
  -- wk-KLP  is not a legal rewrite rule, since the following variables are not bound by the left hand side:  P
  -- when checking the pragma REWRITE wk-KLP

  wk-KLP : ∀{Γ} (A : Ty Γ) {Δ} (τ : Δ ≤ Γ) {Φ} (ρ : Mor Φ Δ) → T⟦ A [ τ ]T ⟧ ρ ≡ T⟦ A ⟧ (τ⦅ τ ⦆ ∘ ρ)
  wk-KLP (dat k i) τ ρ = {!!}  -- Need naturality for F⟦_⟧
  wk-KLP unit τ ρ = refl
  wk-KLP (pi A B) τ ρ = {!!}  -- Need clever "with"
  {-# REWRITE wk-KLP #-}  -- issue #3059, cannot add this as rewrite rule

  C⟦_⟧ : (Γ {Δ} : RC) (ρ : RMor Δ Γ) → Set₁
  C⟦ ε ⟧ _ = Lift ⊤
  C⟦ Γ ▻ A ⟧ ρ = C⟦ Γ ⟧ (proj₁ ∘′ ρ) × T⟦ A ⟧ (proj₁ ∘′ ρ) (proj₂ ∘ ρ)

  fundv : ∀{Γ Δ A} (x : Var (Γ) A) {ρ : RMor Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ ρ) → T⟦ A ⟧ ρ (V⦅ x ⦆ ∘ ρ)
  fundv (vz A) ⟦ρ⟧ = {!proj₂ ⟦ρ⟧!}
  fundv (vs A B x) ⟦ρ⟧ = {!!}

{-
  fund : ∀{Γ Δ A} (t : Tm (ElC Γ) A) {ρ : RMor Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ ρ) → T⟦ A ⟧ ρ (E⦅ t ⦆ ∘ ρ)
  fund (con c) ⟦ρ⟧ = {!!}
  fund (var x) ⟦ρ⟧ = {!!}
  fund (abs A t) ⟦ρ⟧ = {!!}
  fund (app t u) ⟦ρ⟧ = {!!}

-- -}
-- -}
-- -}
-- -}
-- -}
