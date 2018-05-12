-- Codes for contexts and dependent types over a signature of type constructors

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}
-- {-# OPTIONS --no-caching #-}

open import Level using (Lift)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product as Prod using (Σ; ∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

{-# BUILTIN REWRITE _≡_ #-}

module Types where

-- Contexts

mutual
  data Cxt : Set₁ where
    ε : Cxt
    _▷_ : (Γ : Cxt) (S : Fam Γ) → Cxt

  Fam : Cxt → Set₁
  Fam Γ = C⦅ Γ ⦆ → Set

  C⦅_⦆ : Cxt → Set
  C⦅ ε ⦆ = ⊤
  C⦅ Γ ▷ S ⦆ = Σ C⦅ Γ ⦆ S
  -- Note: C⦅_⦆ is constructor headed

Mor : (Δ Γ : Cxt) → Set
Mor Δ Γ = C⦅ Δ ⦆ → C⦅ Γ ⦆

-- Types (families)

Π : ∀{C : Set} (A : C → Set) (B : Σ C A → Set) (γ : C) → Set
Π A B = λ γ → (x : A γ) → B (γ , x)

module Univ (TyC : Set) (Ind : TyC → Cxt) (F⦅_⦆ : (k : TyC) → C⦅ Ind k ⦆ → Set) where

  mutual
    data Ty (Γ : Cxt) : Set where
      unit : Ty Γ
      con  : (k : TyC) (i : C⦅ Ind k ⦆) → Ty Γ
      pi   : (A : Ty Γ) (B : Ty (Γ ≻ A )) → Ty Γ

    _≻_ : (Γ : Cxt) (A : Ty Γ) → Cxt
    Γ ≻ A = Γ ▷ T⦅ A ⦆

    T⦅_⦆ : ∀{Γ} (A : Ty Γ) → Fam Γ
    T⦅ con k i ⦆ _ = F⦅ k ⦆ i
    T⦅ unit   ⦆ _ = ⊤
    T⦅ pi A B ⦆ = Π T⦅ A ⦆ T⦅ B ⦆
    -- T⦅ pi A B ⦆ γ = (x : T⦅ A ⦆ γ) → T⦅ B ⦆ (γ , x)

  Fun : (Γ : Cxt) (A : Ty Γ) → Set
  Fun Γ A = (γ : C⦅ Γ ⦆) → T⦅ A ⦆ γ

  Fun' : (Δ {Γ} : Cxt) (A : Ty Γ) (σ : Mor Δ Γ) → Set
  Fun' Δ A σ = (δ : C⦅ Δ ⦆) → T⦅ A ⦆ (σ δ)

  ext : ({Δ Γ} : Cxt) (σ : Mor Δ Γ) (A : Ty Γ) (a : Fun' Δ A σ) → Mor Δ (Γ ≻ A)
  ext σ A a = λ δ → σ δ , a δ

  -- Kripke application

  kapp : ∀{C D : Set}{A : C → Set} {B : (c : C) → A c → Set}
         (f : (c : C) (a : A c) → B c a) (τ : D → C) (a : (d : D) → A (τ d)) →
         (d : D) → B (τ d) (a d)
  kapp f τ a = λ d → f (τ d) (a d)

  -- Kripke predicate

  KPred : ∀ Γ (A : Ty Γ) → Set₂
  KPred Γ A = ∀ {Δ} (σ : Mor Δ Γ) (f : Fun' Δ A σ) → Set₁

  Mon : ∀{Γ} (A : Ty Γ) (𝓐 : KPred Γ A) → Set₁
  Mon {Γ} A 𝓐 = ∀ {Δ} {σ : Mor Δ Γ} {f : Fun' Δ A σ} (⟦f⟧ : 𝓐 σ f) {Φ} (σ′ : Mor Φ Δ) → 𝓐 (σ ∘ σ′) (f ∘ σ′)

  record LF-KLP-Base : Set₂ where
    field
      F⟦_⟧  : ∀ (k : TyC) (i : C⦅ Ind k ⦆) {Γ} → KPred Γ (con k i)
      monF : ∀ (k : TyC) (i : C⦅ Ind k ⦆) {Γ} → Mon {Γ} (con k i) (F⟦ k ⟧ i)

  module LF-KLP-Ext (P : LF-KLP-Base) (open LF-KLP-Base P) where

    T⟦_⟧ : ∀{Γ} (A : Ty Γ) {Δ} (σ : Mor Δ Γ) (f : Fun' Δ A σ) → Set₁
    T⟦ con k i ⟧ = F⟦ k ⟧ i
    T⟦ unit ⟧ σ _ = Lift ⊤
    T⟦ pi A B ⟧ {Δ} σ f =  ∀{Φ} (σ′ : Mor Φ Δ) {d : Fun' Φ A (σ ∘′ σ′)}
      → (⟦d⟧ : T⟦ A ⟧ (σ ∘′ σ′) d)
      → T⟦ B ⟧ (ext (σ ∘′ σ′) A d) (kapp f σ′ d )

    monT : ∀{Γ} (A : Ty Γ) → Mon A T⟦ A ⟧
    monT (con k i) = monF k i
    monT unit     ⟦f⟧ σ′ = _
    monT (pi A B) ⟦f⟧ σ′ σ″ ⟦d⟧ = ⟦f⟧ (σ′ ∘′ σ″) ⟦d⟧


{-
_×̇_ : ∀{A C : Set} {B : A → Set} {D : C → Set}
     (f : A → C) (g : ∀ a → B a → D (f a)) → Σ A B → Σ C D
(f ×̇ g) (x , y) = f x , g x y

-- Order preserving projections

mutual
  data _≤_ : (Δ Γ : Cxt) → Set₁ where
    id≤  : ∀{Γ} → Γ ≤ Γ
    weak : ∀{Γ Δ S} (τ : Δ ≤ Γ) → (Δ ▷ S) ≤ Γ
    lift' : ∀{Γ Δ S S'} (τ : Δ ≤ Γ) (p : S' ≡ (S ∘′ τ⦅ τ ⦆)) → (Δ ▷ S') ≤ (Γ ▷ S)

  τ⦅_⦆ : ∀{Γ Δ} (τ : Δ ≤ Γ) → C⦅ Δ ⦆ → C⦅ Γ ⦆
  τ⦅ id≤ ⦆ = id
  τ⦅ weak τ ⦆ = τ⦅ τ ⦆ ∘ proj₁
  τ⦅ lift' {S' = S'} τ p ⦆ = τ⦅ τ ⦆ ×̇ λ _ → subst (λ Z → ∀{x} → S' x → Z x) p id

pattern lift {Γ Δ S} τ = lift' {Γ} {Δ} {S} τ refl

-- Identity and first functor law

data IsId : ∀ {Γ} (τ : Γ ≤ Γ) → Set where
  is-id-id  : ∀{Γ} → IsId {Γ} id≤
  is-id-lift : ∀{Γ τ S} (is : IsId {Γ} τ) p → IsId {Γ ▷ S} (lift' τ p)
-- isId : ∀ {Γ} (τ : Γ ≤ Γ) → Set
-- isId id≤ = ⊤
-- isId (weak τ) = ⊥
-- isId (lift' τ p) = {!!}

ar-id' : ∀{Γ} {τ} (is : IsId {Γ} τ) → τ⦅ τ ⦆ ≡ id
ar-id' is-id-id = refl
ar-id' (is-id-lift {Γ} {τ} {S} is p) rewrite ar-id' is = aux p
  where
  aux : (p : S ≡ S) →
      (_×̇_ {C⦅ Γ ⦆} {C⦅ Γ ⦆} {S} {S} id
       (λ z → subst (λ Z → {x : C⦅ Γ ⦆} → S x → Z x) p id))
      ≡ id
  aux refl = refl

-- ar-id : ∀{Γ} → τ⦅ id≤ {Γ} ⦆ ≡ id
-- ar-id = refl -- ar-id' is-id-id

-- {-# REWRITE ar-id' #-}  -- Not a rewrite rule, since is is not bound by lhs

-- postulate
--   lift-id : ∀{Γ S p} → lift' {Γ} {Γ} {S} {S} id≤ p ≡ id≤

-- {-# REWRITE lift-id #-}

-- Composition and second functor law

mutual
  _∙_ : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → Φ ≤ Γ
  τ      ∙ id≤ = τ
  τ      ∙ weak τ′ = weak (τ ∙ τ′)
  id≤    ∙ lift τ′ = lift τ′
  weak τ ∙ lift τ′ = weak (τ ∙ τ′)
  lift {S = S} τ ∙ lift τ′ = (lift' (τ ∙ τ′) (cong (S ∘′_) (sym (ar-comp τ τ′))))
--    = subst (λ z → (_ ▷ (S ∘′ z)) ≤ (_ ▷ S)) (ar-comp τ τ′)
 --   = subst (λ z → (_ ▷ (S ∘′ z)) ≤ (_ ▷ S)) (ar-comp τ τ′) (lift (τ ∙ τ′))

  ar-comp : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → τ⦅ τ ∙ τ′ ⦆ ≡ τ⦅ τ ⦆ ∘′ τ⦅ τ′ ⦆
  ar-comp τ id≤      = refl
  ar-comp τ (weak τ′) rewrite ar-comp τ τ′ = refl
  ar-comp id≤ (lift τ′) = refl
  ar-comp (weak τ) (lift τ′) rewrite ar-comp τ τ′ = refl
  ar-comp (lift {S = S} τ) (lift τ′) rewrite ar-comp τ τ′ = refl
  -- | lift {S = S} (τ ∙ τ′)
  -- ar-comp (lift {S = S} τ) (lift τ′) = {! ar-comp τ τ′!}
  -- with ar-comp τ τ′ | lift {S = S} (τ ∙ τ′)
  -- ... | y | z = {!y!}
  -- ar-comp (lift {S = S} τ) (lift τ′) with ar-comp τ τ′ | lift {S = S} (τ ∙ τ′)
  -- ... | y | z = {!y!}

{-# REWRITE ar-comp #-}

-- Holds definitionally:

test-comp-weak :  ∀{Γ Δ Φ} {S : Fam Φ} {τ : Δ ≤ Γ} {τ′ : Φ ≤ Δ} →  τ ∙ weak {S = S} τ′ ≡ weak (τ ∙ τ′)
test-comp-weak = refl

postulate
  id-comp : ∀{Γ Δ} (τ : Δ ≤ Γ) → id≤ ∙ τ ≡ τ

{-# REWRITE id-comp #-}

test-weak-comp-lift : ∀{Γ Δ} {S : Fam Γ} {τ : Δ ≤ Γ} → weak id≤ ∙ lift {S = S} τ ≡ weak {S = S ∘′ τ⦅ τ ⦆} τ
test-weak-comp-lift = refl

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

-- Identity weakening

{-
{-# TERMINATING #-}
wkT-id' : ∀{Γ} τ (is : IsId τ) (A : Ty Γ) → A [ τ ]T ≡ A
wkT-id' τ is unit = refl
-- wkT-id' τ is (pi A B) = {! (is-id-lift is (cong (T⦅ A [ τ ]T ⦆ ∘′_) (sym (ar-id' is))))!}
wkT-id' {Γ} τ is (pi A B) = {! aux (A [ τ ]T) (wkT-id' τ is A) (B [ lift' τ (denT-wk A τ) ]T) !}
wkT-id' {Γ} τ is (pi A B)
  with A [ τ ]T                     | wkT-id' τ is A
    | B [ lift' τ (denT-wk A τ) ]T -- | wkT-id' (lift' τ (denT-wk A τ)) (is-id-lift is) B
    | wkT-id' (lift' τ (cong (T⦅ A [ τ ]T ⦆ ∘′_) (sym (ar-id' is)))) (is-id-lift is (cong (T⦅ A [ τ ]T ⦆ ∘′_) (sym (ar-id' is)))) (subst (λ A → Ty (Γ ▷ T⦅ A ⦆)) (sym (wkT-id' τ is A)) B)
-- (subst (λ A → Ty (Γ ▷ A)) (sym (ar-id' is)) B)
... | A' | y | B' | z = {!!}
--   -- pi (A [ τ ]T) (B [ lift' τ (denT-wk A τ) ]T) ≡ pi A B
-}

-- TODO
postulate
  wkT-id : ∀{Γ} (A : Ty Γ) → A [ id≤ ]T ≡ A

-- wkT-id : ∀{Γ} (A : Ty Γ) → A [ id≤ ]T ≡ A
-- wkT-id unit = refl
-- wkT-id (pi A B) with A [ id≤ ]T | wkT-id A | denT-wk A id≤ | B [ lift' id≤ (denT-wk A id≤) ]T | wkT-id B
-- -- ... | A' | z | y | B' | z' = {!!}
-- wkT-id (pi A B) | .A | refl | refl | B' | z' = {!!}

{-# REWRITE wkT-id #-}

-- TODO
postulate
  wkT-comp : ∀{Γ Δ Φ} (A : Ty Γ) (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → ((A [ τ ]T) [ τ′ ]T) ≡ (A [ τ ∙ τ′ ]T)

{-# REWRITE wkT-comp #-}

-- Instantiating types (substitution)

mutual

  -- Substitution

  inst : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) → Ty Δ
  inst unit Δ f = unit
  inst (pi A B) Δ f = pi (inst A Δ f)
                         (inst B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f))

  denT-inst : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) (δ : C⦅ Δ ⦆) → T⦅ inst A Δ f ⦆ δ → T⦅ A ⦆ (f δ)
  denT-inst A Δ f δ x =  subst (λ z → z δ) (denT-inst-eq A Δ f) x

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

  -- denT-inst-eq {Γ} (pi A B) Δ f = aux
  --      T⦅ inst A Δ f ⦆
  --      (T⦅ A ⦆ ∘ f)
  --      (denT-inst-eq A Δ f)
  --      T⦅ inst B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f) ⦆
  --      (T⦅ B ⦆ ∘ (f ×̇ denT-inst A Δ f))
  --      (denT-inst-eq B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f))
  --      (T⦅ B ⦆ ∘ (Prod.map f id))
  --      (aux2 T⦅ inst A Δ f ⦆ (T⦅ A ⦆ ∘ f) T⦅ B ⦆ (denT-inst-eq A Δ f))

  --  where
  --  aux : (A₁ A₃ : C⦅ Δ ⦆ → Set)
  --     → (p : A₁ ≡ A₃)
  --     → (B₁ B₂ : Σ C⦅ Δ ⦆ A₁ → Set)
  --     → (q : B₁ ≡ B₂)
  --     → (B₃ : Σ C⦅ Δ ⦆ A₃ → Set)
  --     → (r : subst (λ A →  Σ C⦅ Δ ⦆ A → Set) p B₂ ≡ B₃)
  --     → (λ γ → (x : A₁ γ) → B₁ (γ , x)) ≡ (λ γ → (x : A₃ γ) → B₃ (γ , x))
  --  aux _ _ refl _ _ refl _ refl = refl

  --  aux2 : (A₁ A₃ : C⦅ Δ ⦆ → Set) (p : A₁ ≡ A₃)
  --     → (B₃ : Σ C⦅ Δ ⦆ A₃ → Set)
  --      → subst (λ A → Σ C⦅ Δ ⦆ A → Set) p
  --         (λ x → B₃ (f (x .proj₁) , subst (λ z → z (x .proj₁)) p (x .proj₂)))
  --      ≡ B₃ ∘ Prod.map f id
  --  aux2 _ _ refl _ = refl

   -- aux2 : (A' : C⦅ Δ ⦆ → Set) (p : A' ≡ T⦅ A ⦆ ∘ f) →
   --     subst (λ A'' → Σ C⦅ Δ ⦆ A'' → Set) p
   --        (λ x → T⦅ B ⦆ (f (x .proj₁) , subst (λ z → z (x .proj₁)) p (x .proj₂)))
   --     ≡ T⦅ B ⦆ ∘ Prod.map f id
   -- aux2 _ refl = refl

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


  -- denT-inst : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) (δ : C⦅ Δ ⦆) → T⦅ inst A Δ f ⦆ δ → T⦅ A ⦆ (f δ)
  -- denT-inst {Γ} unit Δ f δ x = _
  -- denT-inst {Γ} (pi A B) Δ f δ g a = {!denT-inst B (Δ ▷ ?) (g (denT-inst' A Δ f δ a))!}

  -- denT-inst' : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) (δ : C⦅ Δ ⦆) → T⦅ A ⦆ (f δ) → T⦅ inst A Δ f ⦆ δ
  -- denT-inst' unit Δ f δ _ = _
  -- denT-inst' (pi A A₁) Δ f δ g a = {!!}

-- {-# REWRITE denT-inst-eq #-}

-- mutual
--   T⟦_⟧ : ∀{Γ} (A : Ty Γ) {Δ} (τ : Δ ≤ Γ) → Fun Δ (A [ τ ]T) → Set₁
--   T⟦ unit ⟧ τ f = Lift ⊤
--   T⟦ pi A B ⟧ {Δ} τ f = ∀{Φ} (σ : Φ ≤ Δ) {d : Fun Φ (A [ τ ∙ σ ]T)}
--     → (⟦d⟧ : T⟦ A ⟧ (τ ∙ σ) d)
--     → T⟦ {!inst B Φ ?!} ⟧ id≤ (kapp f τ⦅ σ ⦆  d )
--    -- REWRITE ar-comp, denT-wk

-- -- Syntax with semantic type codes

-- data Var : (Γ : Cxt) (A : Ty Γ) → Set₁ where
--   vz : ∀{Γ} A                 → Var (Γ ≻ A) (A [ weak id≤ ]T)
--   vs : ∀{Γ} A B (x : Var Γ A) → Var (Γ ≻ B) (A [ weak id≤ ]T)

-- -- Weakening variables

-- _[_]ᵛ : ∀{Γ Δ A} (x : Var Γ A) (τ : Δ ≤ Γ) → Var Δ (A [ τ ]T)
-- x    [ id≤    ]ᵛ = x  -- REWRITE wkT-id
-- _[_]ᵛ {Γ} {Δ} {A} x    (weak {S = S} τ) =  vs (A [ τ ]T) {!!} (x [ τ ]ᵛ)
-- -- x    [ weak τ ]ᵛ =  vs {!.A [ τ ]T!} {!!} (x [ τ ]ᵛ)
-- (vz A) [ lift {Γ} {Δ} τ ]ᵛ =  vz (A [ τ ]T)  -- REWRITE denT-wk
-- vs A B x [ lift τ ]ᵛ =  vs (A [ τ ]T) (B [ τ ]T) (x [ τ ]ᵛ)

-- Syntax with semantic type codes

data Var : (Γ : Cxt) (A : Ty Γ) → Set₁ where
  vz : ∀{Γ} A                 → Var (Γ ≻ A) (A [ weak id≤ ]T)
  vs : ∀{Γ} A S (x : Var Γ A) → Var (Γ ▷ S) (A [ weak id≤ ]T)

-- Weakening variables

_[_]ᵛ : ∀{Γ Δ A} (x : Var Γ A) (τ : Δ ≤ Γ) → Var Δ (A [ τ ]T)
x          [ id≤    ]ᵛ = x  -- REWRITE wkT-id
_[_]ᵛ {A = A} x (weak {S = S} τ) =  vs (A [ τ ]T) S (x [ τ ]ᵛ)
(vz A)     [ lift τ ]ᵛ =  vz (A [ τ ]T)  -- REWRITE denT-wk
(vs A S x) [ lift τ ]ᵛ =  vs (A [ τ ]T) (S ∘′ τ⦅ τ ⦆) (x [ τ ]ᵛ)

-- -}
-- -}
-- -}
-- -}
-- -}
