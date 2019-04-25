-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, May/June 2018

-- 0. Standard library imports and auxiliary definitions

-- We use Agda's rewriting facility to automatically apply proven equalities.

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

module Library where

open import Level                                 public using (Level; _⊔_; Lift) renaming (zero to lzero; suc to lsuc)

open import Data.Empty                            public using (⊥; ⊥-elim)
open import Data.Unit                             public using (⊤)
open import Data.Product                          public using (Σ; ∃; _×_; _,_; proj₁; proj₂; curry; uncurry; <_,_>)
open import Data.Sum                              public using (_⊎_; inj₁; inj₂; [_,_])

open import Data.Nat.Base                         public using (ℕ; zero; suc; _+_)
open import Data.Fin                              public using (Fin; zero; suc; _≟_; fromℕ)
open import Data.Vec                              public using (Vec; []; _∷_; lookup)
-- open import Data.W                                public using (sup) renaming (W to 𝕎) hiding (module W)
-- module 𝕎 = Data.W

open import Function                              public using (id; _∘_; _∘′_; case_of_)

open import Relation.Nullary                      public using (Dec; yes; no)
open import Relation.Nullary.Decidable            public using (True)
open import Relation.Binary                       public using (Decidable)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl; subst; cong; cong₂; cong-app; sym; trans; module ≡-Reasoning)

open import Axiom.Extensionality.Propositional    public using (Extensionality)

{-# BUILTIN REWRITE _≡_ #-}

postulate
  funExt : ∀{a b} → Extensionality a b
  funExt-β : ∀{a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
      (eq : ∀ x → f x ≡ g x) → ∀ a → (P : B a → Set) → ∀ u → subst (λ f → P (f a)) (funExt eq) u ≡ subst P (eq a) u

-- Function extensionality for hidden function

funExtH : ∀{a b}
  {A : Set a} {B : A → Set b} {f g : {x : A} → B x} →
  (∀{x} → f {x} ≡ g {x}) → (λ{x} → f {x}) ≡ (λ{x} → g {x})
funExtH {f = f} {g = g} h = cong (λ f {x} → f x) (funExt {f = λ x → f {x}} {g = λ x → g {x}} (λ x → h {x}))

hcong₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
        (f : (x : A) → B x → C) {x y} {u : B x} {v : B y} (p : x ≡ y) → subst B p u ≡ v → f x u ≡ f y v
hcong₂ f refl refl = refl

subst-ext : ∀{a b p} {A : Set a} {B : Set b} (P : B → Set p)
  → ∀{f g : A → B} (eq : ∀ x → f x ≡ g x)
  → ∀{x : A} (h : P (f x))
  → subst P (eq x) h ≡ subst (λ f → P (f x)) (funExt eq) h
subst-ext P eq {x} h with eq x | funExt eq
subst-ext P eq {x} h | refl | refl = refl

-- Binary product of functions

_×̇′_ : ∀{A B C D : Set} → (A → C) → (B → D) → A × B → C × D
f ×̇′ g = < f ∘ proj₁ , g ∘ proj₂ >

_×̇_ : ∀{a b c d} {A : Set a} {B : A → Set b} {C : Set c} {D : C → Set d}
      → (f : A → C) → (g : ∀{a} → B a → D (f a)) → Σ A B → Σ C D
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

-- Indexed function space

_→̇_ : {I : Set} (A B : I → Set) → Set
A →̇ B = ∀{i} (u : A i) → B i

-- 𝕎 type

module 𝕎 where

  data 𝕎 {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    sup : (c : A) (f : B c → 𝕎 A B) → 𝕎 A B

  head : ∀{a b} {A : Set a} {B : A → Set b} → 𝕎 A B → A
  head (sup c f) = c

  tail : ∀{a b} {A : Set a} {B : A → Set b} (w : 𝕎 A B) → B (head w) → 𝕎 A B
  tail (sup c f) = f

  map : ∀{a a' b b'} {A : Set a} {A' : Set a'} {B : A → Set b} {B' : A' → Set b'}
    (f : A → A') (g : ∀ a → B' (f a) → B a ) → 𝕎 A B → 𝕎 A' B'
  map f g (sup c h) = sup (f c) (map f g ∘ h ∘ g _)

open 𝕎 public hiding (module 𝕎)

𝕎-eta : ∀ {a b} {A : Set a} {B : A → Set b} (w : 𝕎 A B) → 𝕎 A B
𝕎-eta w = sup (𝕎.head w) (𝕎.tail w)

𝕎-map-id : ∀ {a b} {A : Set a} {B : A → Set b} (x : 𝕎 A B) → 𝕎.map id (λ a → id) x ≡ x
𝕎-map-id (sup x f) = hcong₂ sup refl (funExt (λ b → 𝕎-map-id (f b)))

-- Path into a 𝕎-tree to a node that satisfies a property.
-- Similar to the EF operator of CTL.

data EF𝕎 {a b p} {A : Set a} {B : A → Set b} (P : A → Set p) : 𝕎 A B → Set (b ⊔ p) where
  here  : ∀{x f} (p : P x) → EF𝕎 P (sup x f)
  there : ∀{x f} (i : B x) (p : EF𝕎 P (f i)) → EF𝕎 P (sup x f)

EF𝕎-map₀ : ∀ {a b c d p} {A : Set a} {B : A → Set b} {C : Set c} {D : C → Set d} {P : C → Set p}
         (A→C : A → C) (D→B : ∀ a → D (A→C a) → B a)
  (w : 𝕎 A B) (p : EF𝕎 {B = D} P (𝕎.map A→C D→B w)) → EF𝕎 (P ∘ A→C) w
EF𝕎-map₀ A→C D→B (sup x f) (here p)    = here p
EF𝕎-map₀ A→C D→B (sup x f) (there i p) = there (D→B _ i) (EF𝕎-map₀ A→C D→B (f (D→B _ i)) p)

EF𝕎-map : ∀ {a b c d p q} {A : Set a} {B : A → Set b} {C : Set c} {D : C → Set d} {P : C → Set p} {Q : A → Set q}
  (A→C : A → C)
  (D→B : ∀ a → D (A→C a) → B a)
  (P→Q : ∀ a → P (A→C a) → Q a)
  (w : 𝕎 A B) (p : EF𝕎 {B = D} P (𝕎.map A→C D→B w)) → EF𝕎 Q w
EF𝕎-map A→C D→B P→Q (sup x f) (here p)    = here (P→Q _ p)
EF𝕎-map A→C D→B P→Q (sup x f) (there i p) = there (D→B _ i) (EF𝕎-map A→C D→B P→Q (f (D→B _ i)) p)

-- EF𝕎-map : ∀ {a b c d p q} {A : Set a} {B : A → Set b} {C : Set c} {D : C → Set d} {P : A → Set p} {Q : C → Set q}
--   (A→C : A → C)
--   (D→B : ∀ a → D (A→C a) → B a)
--   (P→Q : ∀ a → P a → Q (A→C a))
--   (w : 𝕎 A B) (p : EF𝕎 P w) → EF𝕎 {B = D} Q (𝕎.map A→C D→B w)
-- EF𝕎-map A→C D→B P→Q (sup x f) (here p)    = here (P→Q _ p)
-- EF𝕎-map A→C D→B P→Q (sup x f) (there i p) = there {! (D→B _ i) !} (EF𝕎-map A→C D→B P→Q (f {! i !}) {! p !})

𝕎-lookup : ∀ {a b p} {A : Set a} {B : A → Set b} {P : A → Set p}
  (w : 𝕎 A B) (p : EF𝕎 P w) → Σ A P
𝕎-lookup (sup x f) (here p)    = x , p
𝕎-lookup (sup x f) (there i p) = 𝕎-lookup (f i) p

𝕎-lookup' : ∀ {a b p c} {A : Set a} {B : A → Set b} {P : A → Set p} {C : Set c}
  (w : 𝕎 A B) (p : EF𝕎 P w) (k : (a : A) → P a → C) → C
𝕎-lookup' (sup x f) (here p)    k = k x p
𝕎-lookup' (sup x f) (there i p) k = 𝕎-lookup' (f i) p k

-- 𝕄-types (non-wellfounded trees)

record 𝕄 {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  coinductive; constructor inf; field
    shape : A
    child : B shape → 𝕄 A B
open 𝕄 public

record Eq𝕄 {a b} {A : Set a} {B : A → Set b} (m m' : 𝕄 A B) : Set (a ⊔ b) where
  coinductive; constructor eq-inf; field
    eq-shape : m .shape ≡ m' . shape
    eq-child : ∀ (b : B (m .shape)) → Eq𝕄 (m .child b) (m' .child (subst B eq-shape b))
open Eq𝕄 public

-- Postulate extensionality for 𝕄-types

postulate
  Eq𝕄-to-≡ : ∀ {a b} {A : Set a} {B : A → Set b} {m m' : 𝕄 A B} → Eq𝕄 m m' → m ≡ m'
  Eq𝕄-to-≡-refl : ∀ {a b} {A : Set a} {B : A → Set b} {m : 𝕄 A B} (eq : Eq𝕄 m m) → Eq𝕄-to-≡ eq ≡ refl
{-# REWRITE Eq𝕄-to-≡-refl #-}

-- Map for 𝕄

module _ {a b c d} {A : Set a} {B : A → Set b} {C : Set c} {D : C → Set d}
         (A→C : A → C) (D→B : ∀ a → D (A→C a) → B a) where

 𝕄-map : 𝕄 A B → 𝕄 C D
 𝕄-map m .shape = A→C (m .shape)
 𝕄-map m .child = 𝕄-map ∘ m .child ∘ D→B (m .shape)

-- First functor law

𝕄-map-id' : ∀ {a b} {A : Set a} {B : A → Set b} (x : 𝕄 A B) → Eq𝕄 (𝕄-map id (λ a → id) x) x
𝕄-map-id' x .eq-shape = refl
𝕄-map-id' x .eq-child b = 𝕄-map-id' (x .child b)

𝕄-map-id : ∀ {a b} {A : Set a} {B : A → Set b} (x : 𝕄 A B) → 𝕄-map id (λ a → id) x ≡ x
𝕄-map-id = Eq𝕄-to-≡ ∘ 𝕄-map-id'

-- Pathes into 𝕄-types

data EF𝕄 {a b p} {A : Set a} {B : A → Set b} (P : A → Set p) (m : 𝕄 A B) : Set (b ⊔ p) where
  here  : (p : P (m .shape)) → EF𝕄 P m
  there : (i : B (m .shape)) (p : EF𝕄 P (m .child i)) → EF𝕄 P m


EF𝕄-map : ∀ {a b c d p q} {A : Set a} {B : A → Set b} {C : Set c} {D : C → Set d} {P : C → Set p} {Q : A → Set q}
  (A→C : A → C)
  (D→B : ∀ a → D (A→C a) → B a)
  (P→Q : ∀ a → P (A→C a) → Q a)
  (m : 𝕄 A B) (p : EF𝕄 {B = D} P (𝕄-map A→C D→B m)) → EF𝕄 Q m

EF𝕄-map A→C D→B P→Q m (here p)    = here (P→Q _ p)
EF𝕄-map A→C D→B P→Q m (there i p) = there (D→B _ i) (EF𝕄-map A→C D→B P→Q (m .child (D→B _ i)) p)


𝕄-lookup : ∀ {a b p} {A : Set a} {B : A → Set b} {P : A → Set p}
  (m : 𝕄 A B) (p : EF𝕄 P m) → Σ A P
𝕄-lookup m (here p)    = m .shape , p
𝕄-lookup m (there i p) = 𝕄-lookup (m .child i) p

-- -}
-- -}
-- -}
-- -}
-- -}
