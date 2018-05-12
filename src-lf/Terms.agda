
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Level using (Lift)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product as Prod using (Σ; ∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import Types

module Terms
  (TyC : Set) (Ind : TyC → Set) (F⦅_⦆ : (k : TyC) → Ind k → Set) (open Univ TyC Ind F⦅_⦆)
  (Const : Set) (ty : Const → Ty ε) (c⦅_⦆ : (c : Const) → T⦅ ty c ⦆ _) (open Constants Const ty c⦅_⦆)
  where
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

ar-id' : ∀{Γ} {τ} (is : IsId {Γ} τ) → τ⦅ τ ⦆ ≡ id
ar-id' is-id-id = refl
ar-id' (is-id-lift {Γ} {τ} {S} is p) rewrite ar-id' is = aux p
  where
  aux : (p : S ≡ S) →
      (_×̇_ {C⦅ Γ ⦆} {C⦅ Γ ⦆} {S} {S} id
       (λ z → subst (λ Z → {x : C⦅ Γ ⦆} → S x → Z x) p id))
      ≡ id
  aux refl = refl

test-ar-id : ∀{Γ} → τ⦅ id≤ {Γ} ⦆ ≡ id
test-ar-id = refl

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
  weak τ ∙ lift' τ′ _ = weak (τ ∙ τ′)
  lift {S = S} τ ∙ lift τ′ = (lift' (τ ∙ τ′) (cong (S ∘′_) (sym (ar-comp τ τ′))))

  ar-comp : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → τ⦅ τ ∙ τ′ ⦆ ≡ τ⦅ τ ⦆ ∘′ τ⦅ τ′ ⦆
  ar-comp τ id≤      = refl
  ar-comp τ (weak τ′) rewrite ar-comp τ τ′ = refl
  ar-comp id≤ (lift τ′) = refl
  ar-comp (weak τ) (lift τ′) rewrite ar-comp τ τ′ = refl
  ar-comp (lift {S = S} τ) (lift τ′) rewrite ar-comp τ τ′ = refl

{-# REWRITE ar-comp #-}

-- Holds definitionally:

test-comp-weak :  ∀{Γ Δ Φ} {S : Fam Φ} {τ : Δ ≤ Γ} {τ′ : Φ ≤ Δ} →  τ ∙ weak {S = S} τ′ ≡ weak (τ ∙ τ′)
test-comp-weak = refl

postulate
  id-comp : ∀{Γ Δ} (τ : Δ ≤ Γ) → id≤ ∙ τ ≡ τ

{-# REWRITE id-comp #-}

test-weak-comp-lift : ∀{Γ Δ} {S : Fam Γ} {τ : Δ ≤ Γ} → weak id≤ ∙ lift {S = S} τ ≡ weak {S = S ∘′ τ⦅ τ ⦆} τ
test-weak-comp-lift = refl

-- Forgetting the context (Γ ≤ ε)

_≤ε : ∀ Γ → Γ ≤ ε
ε ≤ε        = id≤
(Γ ▷ S) ≤ε  = weak (Γ ≤ε)

emp-comp : ∀ {Γ Δ} (τ : Δ ≤ Γ) → (Γ ≤ε) ∙ τ ≡ Δ ≤ε
emp-comp id≤         = refl
emp-comp (weak τ)    = cong weak (emp-comp τ)
emp-comp (lift' τ p) = cong weak (emp-comp τ)

{-# REWRITE emp-comp #-}

-- Weakening types

mutual
  _[_]T : ∀{Γ Δ} (A : Ty Γ) (τ : Δ ≤ Γ) → Ty Δ
  unit [ τ ]T = unit
  dat k i [ τ ]T = dat k (i ∘′ τ⦅ τ ⦆)
  pi A B [ τ ]T = pi (A [ τ ]T) (B [ lift' τ (denT-wk A τ) ]T)

  denT-wk : ∀{Γ Δ} (A : Ty Γ) (τ : Δ ≤ Γ) → T⦅ A [ τ ]T ⦆ ≡ T⦅ A ⦆ ∘′ τ⦅ τ ⦆
  denT-wk unit      τ = refl
  denT-wk (dat k i) τ = refl
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
  inst (dat k i) Δ f = dat k (i ∘′ f)
  inst (pi A B) Δ f = pi (inst A Δ f)
                         (inst B (Δ ▷ T⦅ inst A Δ f ⦆) (f ×̇ denT-inst A Δ f))

  denT-inst : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) (δ : C⦅ Δ ⦆) → T⦅ inst A Δ f ⦆ δ → T⦅ A ⦆ (f δ)
  denT-inst A Δ f δ x =  subst (λ z → z δ) (denT-inst-eq A Δ f) x

  -- Substitution lemma

  denT-inst-eq : ∀{Γ} (A : Ty Γ) Δ (f : Mor Δ Γ) → T⦅ inst A Δ f ⦆ ≡ T⦅ A ⦆ ∘ f
  denT-inst-eq unit      Δ f = refl
  denT-inst-eq (dat k i) Δ f = refl
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

{-# REWRITE denT-inst-eq #-}


-- Syntax with semantic type codes

-- Variables

data Var : (Γ : Cxt) (A : Ty Γ) → Set₁ where
  vz : ∀{Γ} A                 → Var (Γ ≻ A) (A [ weak id≤ ]T)
  vs : ∀{Γ} A S (x : Var Γ A) → Var (Γ ▷ S) (A [ weak id≤ ]T)

-- Weakening variables

_[_]ᵛ : ∀{Γ Δ A} (x : Var Γ A) (τ : Δ ≤ Γ) → Var Δ (A [ τ ]T)
x          [ id≤    ]ᵛ = x  -- REWRITE wkT-id
_[_]ᵛ {A = A} x (weak {S = S} τ) =  vs (A [ τ ]T) S (x [ τ ]ᵛ)
(vz A)     [ lift τ ]ᵛ =  vz (A [ τ ]T)  -- REWRITE denT-wk
(vs A S x) [ lift τ ]ᵛ =  vs (A [ τ ]T) (S ∘′ τ⦅ τ ⦆) (x [ τ ]ᵛ)

-- Evaluating variables

V⦅_⦆ : ∀{Γ T} → Var Γ T → Fun Γ T
V⦅ vz _     ⦆ = proj₂
V⦅ vs _ _ x ⦆ = V⦅ x ⦆ ∘ proj₁

-- Evaluating weakened variables

wk-evalv : ∀{Γ Δ T} (x : Var Γ T) (τ : Δ ≤ Γ) → V⦅ x [ τ ]ᵛ ⦆ ≡ V⦅ x ⦆ ∘ τ⦅ τ ⦆
wk-evalv x          id≤      = refl
wk-evalv x          (weak τ) = cong (_∘ proj₁) (wk-evalv x τ)
wk-evalv (vz _)     (lift τ) = refl
wk-evalv (vs _ _ x) (lift τ) = cong (_∘ proj₁) (wk-evalv x τ)

-- Terms and their evaluation

apply : ∀{C : Set} {A : C → Set} {B : (c : C) → A c → Set}
  (f : (c : C) (a : A c) → B c a) (d : (c : C) → A c) (c : C) → B c (d c)
apply f a = λ c → f c (a c)

mutual
  data Tm (Γ : Cxt) : (A : Ty Γ) → Set₁ where
    con : (c : Const) → Tm Γ (ty c [ Γ ≤ε ]T)
    var : ∀{A}   (x : Var Γ A) → Tm Γ A
    abs : ∀ (A : Ty Γ) {B : Ty (Γ ≻ A)} (t : Tm (Γ ≻ A) B) → Tm Γ (pi A B)
    app : ∀{A : Ty Γ} {B : Ty (Γ ≻ A)} (t : Tm Γ (pi A B)) (u : Tm Γ A) → Tm Γ (inst B Γ (sg u))

  sg : ∀{Γ A} → Tm Γ A → Mor Γ (Γ ≻ A)
  sg t = λ γ → γ ,  E⦅ t ⦆ γ

  E⦅_⦆ : ∀{Γ A} → Tm Γ A → Fun Γ A
  E⦅ con c ⦆ _ = c⦅ c ⦆
  E⦅ var x ⦆   = V⦅ x ⦆
  E⦅ abs A t ⦆   = curry E⦅ t ⦆
  E⦅ app t u ⦆ =  apply E⦅ t ⦆ E⦅ u ⦆  -- REWRITE denT-inst-eq

-- Weakening terms

_[_]ᵉ : ∀{Γ Δ T} (t : Tm Γ T) (τ : Δ ≤ Γ) → Tm Δ (T [ τ ]T)
con c   [ τ ]ᵉ = con c  -- REWRITE emp-comp
var x   [ τ ]ᵉ = var (x [ τ ]ᵛ)
abs A t [ τ ]ᵉ = abs (A [ τ ]T) (t [ lift' τ (denT-wk A τ) ]ᵉ)
app t u [ τ ]ᵉ = {! app (t [ τ ]ᵉ) (u [ τ ]ᵉ) !}

-- Goal: Tm .Δ (inst .B .Γ (sg u) [ τ ]T)
-- Have: Tm .Δ
--       (inst (.B [ lift' τ (denT-wk .A τ) ]T) .Δ (sg (u [ τ ]ᵉ)))

wk-eval : ∀{Γ Δ T} (t : Tm Γ T) (τ : Δ ≤ Γ) → E⦅ t [ τ ]ᵉ ⦆ ≡ E⦅ t ⦆ ∘ τ⦅ τ ⦆
wk-eval (con c) τ = refl
wk-eval (var x) τ = wk-evalv x τ
-- wk-eval (abs A t) τ rewrite cong curry (wk-eval t (lift' τ (denT-wk A τ))) = {!wk-eval t (lift' τ (denT-wk A τ))!} -- rewrite wk-eval t (lift τ) = refl
wk-eval (abs A t) τ = {!trans (cong curry (wk-eval t (lift' τ (denT-wk A τ)))) ?!} -- rewrite wk-eval t (lift τ) = refl
-- wk-eval (abs A t) τ with  T⦅ A [ τ ]T ⦆ | T⦅ A ⦆ ∘ τ⦅ τ ⦆ | denT-wk A τ | E⦅ t [ lift' τ (denT-wk A τ) ]ᵉ ⦆
-- ... | A' | A'' | eq | Z = ? ---  = {!wk-eval t (lift' τ (denT-wk A τ))!} -- rewrite wk-eval t (lift τ) = refl
wk-eval (app t u) τ = {!!} -- rewrite wk-eval t τ | wk-eval u τ = refl

-- -}
-- -}
-- -}
-- -}
-- -}
