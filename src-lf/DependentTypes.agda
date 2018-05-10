-- Codes for contexts and dependent types

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Data.Unit using (⊤)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

{-# BUILTIN REWRITE _≡_ #-}

module DependentTypes where

_×̇_ : ∀{A C : Set} {B : A → Set} {D : C → Set}
     (f : A → C) (g : ∀{a} → B a → D (f a)) → Σ A B → Σ C D
(f ×̇ g) (x , y) = f x , g y

-- Contexts

mutual
  data Cxt : Set₁ where
    ε : Cxt
    _▷_ : (Γ : Cxt) (U : C⦅ Γ ⦆ → Set) → Cxt

  C⦅_⦆ : Cxt → Set
  C⦅ ε ⦆ = ⊤
  C⦅ Γ ▷ U ⦆ = Σ C⦅ Γ ⦆ U

-- Order preserving projections

mutual
  data _≤_ : (Δ Γ : Cxt) → Set₁ where
    id≤  : ∀{Γ} → Γ ≤ Γ
    weak : ∀{Γ Δ U} (τ : Δ ≤ Γ) → (Δ ▷ U) ≤ Γ
    lift' : ∀{Γ Δ U U'} (τ : Δ ≤ Γ) (p : U' ≡ (U ∘′ τ⦅ τ ⦆)) → (Δ ▷ U') ≤ (Γ ▷ U)

  τ⦅_⦆ : ∀{Γ Δ} (τ : Δ ≤ Γ) → C⦅ Δ ⦆ → C⦅ Γ ⦆
  τ⦅ id≤ ⦆ = id
  τ⦅ weak τ ⦆ = τ⦅ τ ⦆ ∘ proj₁
  τ⦅ lift' {U' = U'} τ p ⦆ = τ⦅ τ ⦆ ×̇ subst (λ Z → ∀{x} → U' x → Z x) p id

pattern lift {Γ Δ U} τ = lift' {Γ} {Δ} {U} τ refl

-- Category and functor laws

mutual
  _∙_ : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → Φ ≤ Γ
  τ      ∙ id≤ = τ
  τ      ∙ weak τ′ = weak (τ ∙ τ′)
  id≤    ∙ lift τ′ = lift τ′
  weak τ ∙ lift τ′ = weak (τ ∙ τ′)
  lift {U = U} τ ∙ lift τ′ = (lift' (τ ∙ τ′) (cong (U ∘′_) (sym (ar-comp τ τ′))))
--    = subst (λ z → (_ ▷ (U ∘′ z)) ≤ (_ ▷ U)) (ar-comp τ τ′)
 --   = subst (λ z → (_ ▷ (U ∘′ z)) ≤ (_ ▷ U)) (ar-comp τ τ′) (lift (τ ∙ τ′))

  ar-comp : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → τ⦅ τ ∙ τ′ ⦆ ≡ τ⦅ τ ⦆ ∘′ τ⦅ τ′ ⦆
  ar-comp τ id≤      = refl
  ar-comp τ (weak τ′) rewrite ar-comp τ τ′ = refl
  ar-comp id≤ (lift τ′) = refl
  ar-comp (weak τ) (lift τ′) rewrite ar-comp τ τ′ = refl
  ar-comp (lift {U = U} τ) (lift τ′) rewrite ar-comp τ τ′ = refl
  -- | lift {U = U} (τ ∙ τ′)
  -- ar-comp (lift {U = U} τ) (lift τ′) = {! ar-comp τ τ′!}
  -- with ar-comp τ τ′ | lift {U = U} (τ ∙ τ′)
  -- ... | y | z = {!y!}
  -- ar-comp (lift {U = U} τ) (lift τ′) with ar-comp τ τ′ | lift {U = U} (τ ∙ τ′)
  -- ... | y | z = {!y!}

{-# REWRITE ar-comp #-}

-- Types (families)

mutual
  data Ty (Γ : Cxt) : Set where
    unit : Ty Γ
    pi   : (A : Ty Γ) (B : Ty (Γ ▷ T⦅ A ⦆)) → Ty Γ

  T⦅_⦆ : ∀{Γ} (A : Ty Γ) → C⦅ Γ ⦆ → Set
  T⦅ unit   ⦆ γ = ⊤
  T⦅ pi A B ⦆ γ = (x : T⦅ A ⦆ γ) → T⦅ B ⦆ (γ , x)

-- Weakening types

mutual
  _[_]T : ∀{Γ Δ} (A : Ty Γ) (τ : Δ ≤ Γ) → Ty Δ
  unit [ τ ]T = unit
  pi A B [ τ ]T = pi (A [ τ ]T) (B [ lift' τ (denT-wk A τ) ]T)

  denT-wk : ∀{Γ Δ} (A : Ty Γ) (τ : Δ ≤ Γ) → T⦅ A [ τ ]T ⦆ ≡ T⦅ A ⦆ ∘′ τ⦅ τ ⦆
  denT-wk unit     τ = refl
  denT-wk (pi A B) τ with T⦅ A [ τ ]T ⦆                     | denT-wk A τ
                        | T⦅ B [ lift' τ (denT-wk A τ) ]T ⦆ | denT-wk B (lift' τ (denT-wk A τ))
  denT-wk (pi A B) τ | .(T⦅ A ⦆ ∘′ τ⦅ τ ⦆) | refl
                     | .(λ γ → T⦅ B ⦆ (τ⦅ τ ⦆ (γ .proj₁) , γ .proj₂)) | refl
                     = refl
