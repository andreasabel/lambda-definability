-- Codes for contexts and dependent types

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Level using (Lift)

open import Data.Unit using (⊤)
open import Data.Product as Prod using (Σ; ∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

{-# BUILTIN REWRITE _≡_ #-}

module DependentTypes where

_×̇_ : ∀{A C : Set} {B : A → Set} {D : C → Set}
     (f : A → C) (g : ∀ a → B a → D (f a)) → Σ A B → Σ C D
(f ×̇ g) (x , y) = f x , g x y

-- Contexts

mutual
  data Cxt : Set₁ where
    ε : Cxt
    _▷_ : (Γ : Cxt) (U : Fam Γ) → Cxt

  Fam : Cxt → Set₁
  Fam Γ = C⦅ Γ ⦆ → Set

  C⦅_⦆ : Cxt → Set
  C⦅ ε ⦆ = ⊤
  C⦅ Γ ▷ U ⦆ = Σ C⦅ Γ ⦆ U

Mor : (Δ Γ : Cxt) → Set
Mor Δ Γ = C⦅ Δ ⦆ → C⦅ Γ ⦆


-- Order preserving projections

mutual
  data _≤_ : (Δ Γ : Cxt) → Set₁ where
    id≤  : ∀{Γ} → Γ ≤ Γ
    weak : ∀{Γ Δ U} (τ : Δ ≤ Γ) → (Δ ▷ U) ≤ Γ
    lift' : ∀{Γ Δ U U'} (τ : Δ ≤ Γ) (p : U' ≡ (U ∘′ τ⦅ τ ⦆)) → (Δ ▷ U') ≤ (Γ ▷ U)

  τ⦅_⦆ : ∀{Γ Δ} (τ : Δ ≤ Γ) → C⦅ Δ ⦆ → C⦅ Γ ⦆
  τ⦅ id≤ ⦆ = id
  τ⦅ weak τ ⦆ = τ⦅ τ ⦆ ∘ proj₁
  τ⦅ lift' {U' = U'} τ p ⦆ = τ⦅ τ ⦆ ×̇ λ _ → subst (λ Z → ∀{x} → U' x → Z x) p id

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

  T⦅_⦆ : ∀{Γ} (A : Ty Γ) → Fam Γ
  T⦅ unit   ⦆ γ = ⊤
  T⦅ pi A B ⦆ γ = (x : T⦅ A ⦆ γ) → T⦅ B ⦆ (γ , x)

Fun : (Γ : Cxt) (A : Ty Γ) → Set
Fun Γ A = (γ : C⦅ Γ ⦆) → T⦅ A ⦆ γ

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

{-# REWRITE denT-wk #-}

-- Instantiating types (substitution)

mutual

  -- Substitution

  inst : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) → Ty Δ
  inst unit Δ f = unit
  inst (pi A B) Δ f = pi (inst A Δ f)
                         (inst B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f))

  -- Substitution lemma

  denT-inst-eq : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) → T⦅ inst A Δ f ⦆ ≡ T⦅ A ⦆ ∘ f
  denT-inst-eq {Γ} unit Δ f = refl
  -- denT-inst-eq {Γ} (pi A B) Δ f = {!!}
  -- denT-inst-eq {Γ} (pi A B) Δ f
  --   with T⦅ inst A Δ f ⦆
  --      | denT-inst-eq A Δ f
  --      | T⦅ inst B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f) ⦆
  -- denT-inst-eq {Γ} (pi A B) Δ f | A' | refl | B' = {!!}
  denT-inst-eq {Γ} (pi A B) Δ f = aux
       T⦅ inst A Δ f ⦆
       (denT-inst-eq A Δ f)
       T⦅ inst B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f) ⦆
       (T⦅ B ⦆ ∘ (f ×̇ denT-inst A Δ f))
       (denT-inst-eq B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f))
       (T⦅ B ⦆ ∘ (Prod.map f id))
       (aux2 T⦅ inst A Δ f ⦆ (denT-inst-eq A Δ f))

   where
   aux : (A' : C⦅ Δ ⦆ → Set)
      → (p : A' ≡ T⦅ A ⦆ ∘ f)
      → (B₁ B₂ : Σ C⦅ Δ ⦆ A' → Set)
      → (q : B₁ ≡ B₂)
      → (B₃ : Σ C⦅ Δ ⦆ (T⦅ A ⦆ ∘ f) → Set)
      → (r : subst (λ A' →  Σ C⦅ Δ ⦆ A' → Set) p B₂ ≡ B₃)
      → (λ γ → (x : A' γ) → B₁ (γ , x)) ≡ (λ γ → (x : T⦅ A ⦆ (f γ)) → B₃ (γ , x))
   aux _ refl _ _ refl _ refl = refl

   aux2 : (A' : C⦅ Δ ⦆ → Set) (p : A' ≡ T⦅ A ⦆ ∘ f) →
       subst (λ A'' → Σ C⦅ Δ ⦆ A'' → Set) p
          (λ x → T⦅ B ⦆ (f (x .proj₁) , subst (λ z → z (x .proj₁)) p (x .proj₂)))
       ≡ T⦅ B ⦆ ∘ Prod.map f id
   aux2 _ refl = refl

   -- goal : subst (λ A' → Σ C⦅ Δ ⦆ A' → Set) (denT-inst-eq A Δ f) (T⦅ B ⦆ ∘ (f ×̇ denT-inst A Δ f))
   --        ≡ T⦅ B ⦆ ∘ Prod.map f id

   -- Goal: (λ γ →
   --       (x : T⦅ inst A Δ f ⦆ γ) →
   --       T⦅ inst B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f) ⦆ (γ , x))
   --    ≡ (λ γ → (x : T⦅ A ⦆ γ) → T⦅ B ⦆ (γ , x)) ∘ f
  -- denT-inst-eq {Γ} (pi A B) Δ f
  --   with T⦅ inst A Δ f ⦆
  --      | denT-inst-eq A Δ f
  --      | T⦅ inst B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f) ⦆
  --      | T⦅ B ⦆ ∘ (f ×̇ denT-inst A Δ f)
  --      | T⦅ B ⦆ ∘ (λ p → (f (proj₁ p) , proj₂ p))
  --      -- | T⦅ B ⦆ ∘ (Prod.map f id)
  --      | denT-inst-eq B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f)
  -- -- denT-inst-eq {Γ} (pi A B) Δ f | .(λ x → T⦅ A ⦆ (f x)) | refl | B' | .B' | refl = {!refl!}
  -- denT-inst-eq {Γ} (pi A B) Δ f | A' | z | B' | B'' | B''' | y = {!!}
  -- -- denT-inst-eq {Γ} (pi A B) Δ f | .(λ x → T⦅ A ⦆ (f x)) | refl | B' | y = {!!}
  -- -- denT-inst-eq : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) (δ : C⦅ Δ ⦆) → T⦅ inst A Δ f ⦆ δ ≡ T⦅ A ⦆ (f δ)
  -- -- denT-inst-eq {Γ} unit Δ f δ = refl
  -- -- denT-inst-eq {Γ} (pi A B) Δ f δ = {!denT-inst B (Δ ▷ ?) (g (denT-inst' A Δ f δ a))!}

  denT-inst : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) (δ : C⦅ Δ ⦆) → T⦅ inst A Δ f ⦆ δ → T⦅ A ⦆ (f δ)
  denT-inst A Δ f δ x =  subst (λ z → z δ) (denT-inst-eq A Δ f) x

  -- denT-inst : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) (δ : C⦅ Δ ⦆) → T⦅ inst A Δ f ⦆ δ → T⦅ A ⦆ (f δ)
  -- denT-inst {Γ} unit Δ f δ x = _
  -- denT-inst {Γ} (pi A B) Δ f δ g a = {!denT-inst B (Δ ▷ ?) (g (denT-inst' A Δ f δ a))!}

  -- denT-inst' : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) (δ : C⦅ Δ ⦆) → T⦅ A ⦆ (f δ) → T⦅ inst A Δ f ⦆ δ
  -- denT-inst' unit Δ f δ _ = _
  -- denT-inst' (pi A A₁) Δ f δ g a = {!!}

{-# REWRITE denT-inst-eq #-}

-- Kripke application

kapp : ∀{C D : Set}{A : C → Set} {B : (c : C) → A c → Set}
       (f : (c : C) (a : A c) → B c a) (τ : D → C) (a : (d : D) → A (τ d)) →
       (d : D) → B (τ d) (a d)
kapp f τ a = λ d → f (τ d) (a d)

-- Kripke predicate

mutual
  T⟦_⟧ : ∀{Γ} (A : Ty Γ) {Δ} (τ : Δ ≤ Γ) → Fun Δ (A [ τ ]T) → Set₁
  T⟦ unit ⟧ τ f = Lift ⊤
  T⟦ pi A B ⟧ {Δ} τ f = ∀{Φ} (σ : Φ ≤ Δ) {d : Fun Φ (A [ τ ∙ σ ]T)} (⟦d⟧ : T⟦ A ⟧ (τ ∙ σ) d) → T⟦ {!!} ⟧ (τ ∙ σ) (kapp f τ⦅ σ ⦆ d)
