-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, May/June 2018

-- 0. Standard library imports and auxiliary definitions

-- We use Agda's rewriting facility to automatically apply proven equalities.

{-# OPTIONS --rewriting #-}

module Library where

open import Level                                 public using (Level; _⊔_; Lift) renaming (zero to lzero; suc to lsuc)

open import Data.Empty                            public using (⊥; ⊥-elim)
open import Data.Unit                             public using (⊤)
open import Data.Product                          public using (Σ; ∃; _×_; _,_; proj₁; proj₂; curry; <_,_>)
open import Data.Sum                              public using (_⊎_; inj₁; inj₂; [_,_])

open import Data.Nat.Base                         public using (ℕ; zero; suc)
open import Data.Fin                              public using (Fin; zero; suc; _≟_; fromℕ)
open import Data.Vec                              public using (Vec; []; _∷_; lookup)
open import Data.W                                public using (sup) renaming (W to 𝕎; map to 𝕎-map)

open import Function                              public using (id; _∘_; _∘′_; case_of_)

open import Relation.Nullary                      public using (Dec; yes; no)
open import Relation.Nullary.Decidable            public using (True)
open import Relation.Binary                       public using (Decidable)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl; subst; cong; cong₂; cong-app; sym; trans; Extensionality; module ≡-Reasoning)

{-# BUILTIN REWRITE _≡_ #-}

postulate
  funExt : Extensionality lzero lzero
  funExt-β :   {A : Set} {B : A → Set} {f g : (x : A) → B x} →
      (eq : ∀ x → f x ≡ g x) → ∀ a → (P : B a → Set) → ∀ u → subst (\ f → P (f a)) (funExt eq) u ≡ subst P (eq a) u

-- Function extensionality for hidden function

funExtH :
  {A : Set} {B : A → Set} {f g : {x : A} → B x} →
  (∀{x} → f {x} ≡ g {x}) → (λ{x} → f {x}) ≡ (λ{x} → g {x})
funExtH {f = f} {g = g} h = cong (λ f {x} → f x) (funExt {f = λ x → f {x}} {g = λ x → g {x}} (λ x → h {x}))

hcong₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
        (f : (x : A) → B x → C) {x y} {u : B x} {v : B y} (p : x ≡ y) → subst B p u ≡ v → f x u ≡ f y v
hcong₂ f refl refl = refl

-- Binary product of functions

_×̇_ : ∀{A B C D : Set} → (A → C) → (B → D) → A × B → C × D
f ×̇ g = < f ∘ proj₁ , g ∘ proj₂ >

-- Binary sum of functions

_+̇_ : ∀{A B C D : Set} (f : A → C) (g : B → D) → A ⊎ B → C ⊎ D
f +̇ g = [ inj₁ ∘ f , inj₂ ∘ g ]

-- _+̇′_ : ∀{A B : Set} {C : A → Set} {D : B → Set} (f : (a : A) → C a) (g : (b : B) → D b) (x : A ⊎ B) → case x of  [ C , D ]
-- f +̇′ g = [ inj₁ ∘ f , inj₂ ∘ g ]
-- (f +̇′ g) (inj₁ a) = f a
-- (f +̇′ g) (inj₂ b) = g b

-- Application (S-combinator)

apply : ∀{A B C : Set} (f : C → A → B) (d : C → A) → C → B
apply f a = λ c → f c (a c)

-- Kronecker symbol

δ : ∀{n} (i j : Fin n) → Set
δ i j = True (i ≟ j)

module DecRefl {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A})) where

  ≟-refl : ∀ a → a ≟ a ≡ yes refl
  ≟-refl a with a ≟ a
  ≟-refl a | yes refl = refl
  ≟-refl a | no ¬p = case ¬p refl of λ()

module DecFinRefl {n} = DecRefl {A = Fin n} _≟_
{-# REWRITE DecFinRefl.≟-refl #-}

-- module _ {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A})) {a : A} where

--   ≟-refl : a ≟ a ≡ yes refl
--   ≟-refl with a ≟ a
--   ≟-refl | yes refl = refl
--   ≟-refl | no ¬p = case ¬p refl of λ()

-- {-# REWRITE ≟-refl #-}

-- Case distinction for Fin

finCase : ∀{ℓ} (C : ∀{n} (i : Fin n) → Set ℓ)
  → (∀{n} → C {suc n} zero)
  → (∀{n} (i : Fin n) → C (suc i))
  → ∀{n} (i : Fin n) → C i
finCase C z s zero    = z
finCase C z s (suc i) = s i

finCase' : ∀{ℓ} {n} (C : (i : Fin (suc n)) → Set ℓ)
  → C zero
  → ((j : Fin n) → C (suc j))
  → (i : Fin (suc n)) → C i
finCase' C z s zero    = z
finCase' C z s (suc i) = s i

-- Path into a 𝕎-tree to a node that satisfies a property.
-- Similar to the EF operator of CTL.

data EF𝕎 {a b p} {A : Set a} {B : A → Set b} (P : A → Set p) : 𝕎 A B → Set (b ⊔ p) where
  here  : ∀{x f} (p : P x) → EF𝕎 P (sup x f)
  there : ∀{x f} (i : B x) (p : EF𝕎 P (f i)) → EF𝕎 P (sup x f)

-- M-types

record 𝕄 {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  coinductive; constructor inf; field
    shape : A
    child : B shape → 𝕄 A B
open 𝕄 public

data EF𝕄 {a b p} {A : Set a} {B : A → Set b} (P : A → Set p) (m : 𝕄 A B) : Set (b ⊔ p) where
  here  : (p : P (m .shape)) → EF𝕄 P m
  there : (i : B (m .shape)) (p : EF𝕄 P (m .child i)) → EF𝕄 P m
