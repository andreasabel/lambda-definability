-- (Meta-level) functions and their characterization by Kripke predicates

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

{-# BUILTIN REWRITE _≡_ #-}

module Fun (Base : Set) (B⦅_⦆ : Base → Set) where

-- Simple types over a set of base types

data Ty : Set where
  base : (b : Base) → Ty
  _⇒_ : (U T : Ty) → Ty

-- Typing contexts

data Cxt : Set where
  ε : Cxt
  _▷_ : (Γ : Cxt) (U : Ty) → Cxt

-- Order-preserving embeddings

data _≤_ : (Γ Δ : Cxt) → Set where
  id≤  : ∀{Γ} → Γ ≤ Γ
  weak : ∀{Γ Δ U} (τ : Γ ≤ Δ) → (Γ ▷ U) ≤ Δ
  lift : ∀{Γ Δ U} (τ : Γ ≤ Δ) → (Γ ▷ U) ≤ (Δ ▷ U)

_∙_ : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → Φ ≤ Γ
τ      ∙ id≤ = τ
τ      ∙ weak τ′ = weak (τ ∙ τ′)
id≤    ∙ lift τ′ = lift τ′
weak τ ∙ lift τ′ = weak (τ ∙ τ′)
lift τ ∙ lift τ′ = lift (τ ∙ τ′)

-- Interpretation of types

T⦅_⦆ : Ty → Set
T⦅ base b ⦆ = B⦅ b ⦆
T⦅ U ⇒ T ⦆ = T⦅ U ⦆ → T⦅ T ⦆

C⦅_⦆ : Cxt → Set
C⦅ ε ⦆ = ⊤
C⦅ Γ ▷ U ⦆ = C⦅ Γ ⦆ × T⦅ U ⦆

Fun : (Γ : Cxt) (T : Ty) → Set
Fun Γ T = C⦅ Γ ⦆ → T⦅ T ⦆

CFun : (Δ Γ : Cxt) → Set
CFun Δ Γ = C⦅ Δ ⦆ → C⦅ Γ ⦆

-- Application (S-combinator)

apply : ∀{A B C : Set} (f : C → A → B) (d : C → A) → C → B
apply f a = λ c → f c (a c)

-- Kripke application

kapp : ∀{A B C D : Set} (f : C → A → B) (τ : D → C) (a : D → A) → D → B
kapp f τ a = λ d → f (τ d) (a d)

-- Arity functors: interpretation of OPE as functions

_×̇_ : ∀{A B C D : Set} → (A → C) → (B → D) → A × B → C × D
(f ×̇ g) (x , y) = f x , g y

Mor : ∀{Γ Δ} (E : Δ ≤ Γ) → Set
Mor {Γ} {Δ} E = C⦅ Δ ⦆ → C⦅ Γ ⦆

Ar : ∀{Γ Δ} (E : Δ ≤ Γ) → Mor E
Ar id≤ = id
Ar (weak E) = Ar E ∘ proj₁
Ar (lift E) = Ar E ×̇ id

-- The second functor law for Ar

ar-comp : ∀{Γ Δ Φ} (τ : Δ ≤ Γ) (τ′ : Φ ≤ Δ) → Ar (τ ∙ τ′) ≡ Ar τ ∘′ Ar τ′
ar-comp τ id≤      = refl
ar-comp τ (weak τ′) rewrite ar-comp τ τ′ = refl
ar-comp id≤ (lift τ′) = refl
ar-comp (weak τ) (lift τ′) rewrite ar-comp τ τ′ = refl
ar-comp (lift τ) (lift τ′) rewrite ar-comp τ τ′ = refl

{-# REWRITE ar-comp #-}

-- Kripke predicate

KPred : (A : Set) → Set₁
KPred A = (Γ : Cxt) (f : C⦅ Γ ⦆ → A) → Set

mon : ∀{A} → KPred A → Set
mon {A} P = ∀{Γ Δ : Cxt} (τ : Δ ≤ Γ) {f : C⦅ Γ ⦆ → A}
  → (⟦f⟧ : P Γ f)
  → P Δ (f ∘′ Ar τ)

-- A Kripke logical predicate is uniquely determined by its definition at base type

record STLC-KLP : Set₁ where
  constructor stlc-klp
  field
    B⟦_⟧  : (b : Base) → KPred B⦅ b ⦆
    monB  : (b : Base) → mon B⟦ b ⟧

-- Kripke logical predicate over the world of context extensions

module STLC-KLP-Ext (P : STLC-KLP) (open STLC-KLP P) where
-- module STLC-KLR (B⟦_⟧ : (b : Base) → KPred B⦅ b ⦆) (monB : ∀ b → mon B⟦ b ⟧) where
-- module KLR (B⟦_⟧ : (b : Base) (Γ : Cxt) (f : C⦅ Γ ⦆ → B⦅ b ⦆) → Set) where

  T⟦_⟧ : (T : Ty) → KPred T⦅ T ⦆
  T⟦ base b ⟧ = B⟦ b ⟧
  T⟦ U ⇒ T ⟧ Γ f =
    ∀{Δ} (τ : Δ ≤ Γ) {d : Fun Δ U}
    →  (⟦d⟧ : T⟦ U ⟧ Δ d)
    →  T⟦ T ⟧ Δ (kapp f (Ar τ) d)

  monT : ∀ T → mon T⟦ T ⟧
  monT (base b) = monB b
  monT (U ⇒ T) {Γ} {Δ} τ {f} ⟦f⟧ {Φ} τ′ {d} ⟦d⟧ = ⟦f⟧ (τ ∙ τ′) {d} ⟦d⟧  -- needs REWRITE ar-comp

-- A function is STLC-definable if it satisfies all STLC-KLPs.
-- This is a "big" proposition.
-- But it is purely semantic, independent from any syntactic definitions.

STLC-definable : ∀ Γ T (f : Fun Γ T) → Set₁
STLC-definable Γ T f = ∀ (P : STLC-KLP) (open STLC-KLP-Ext P) → T⟦ T ⟧ Γ f

-- In the following we prove that a function is STLC-definable iff
-- it is the evaluation of a STLC term.

-- STLC

data Var (T : Ty) : (Γ : Cxt) → Set where
  vz : ∀{Γ} → Var T (Γ ▷ T)
  vs : ∀{Γ U} (x : Var T Γ) → Var T (Γ ▷ U)

data Tm (Γ : Cxt) : (T : Ty) → Set where
  var : ∀{T}   (x : Var T Γ) → Tm Γ T
  abs : ∀{U T} (t : Tm (Γ ▷ U) T) → Tm Γ (U ⇒ T)
  app : ∀{U T} (t : Tm Γ (U ⇒ T)) (u : Tm Γ U) → Tm Γ T

-- Weakening

_w[_]ᵛ : ∀{Γ Δ T} (x : Var T Γ) (τ : Δ ≤ Γ) → Var T Δ
x    w[ id≤    ]ᵛ = x
x    w[ weak τ ]ᵛ = vs (x w[ τ ]ᵛ)
vz   w[ lift τ ]ᵛ = vz
vs x w[ lift τ ]ᵛ = vs (x w[ τ ]ᵛ)

_w[_]ᵉ : ∀{Γ Δ T} (t : Tm Γ T) (τ : Δ ≤ Γ) → Tm Δ T
var x   w[ τ ]ᵉ = var (x w[ τ ]ᵛ)
abs t   w[ τ ]ᵉ = abs (t w[ lift τ ]ᵉ)
app t u w[ τ ]ᵉ = app (t w[ τ ]ᵉ) (u w[ τ ]ᵉ)

-- Evaluation of variables and expressions

V⦅_⦆ : ∀{Γ T} → Var T Γ → Fun Γ T
V⦅ vz ⦆   = proj₂
V⦅ vs x ⦆ = V⦅ x ⦆ ∘′ proj₁

E⦅_⦆ : ∀{Γ T} → Tm Γ T → Fun Γ T
E⦅ var x ⦆   = V⦅ x ⦆
E⦅ abs t ⦆   = curry E⦅ t ⦆
E⦅ app t u ⦆ = apply E⦅ t ⦆ E⦅ u ⦆

-- Evaluation of a term t weakened by τ
-- is the evaluation of t postcomposed with the action of τ.

wk-evalv : ∀{Γ Δ T} (x : Var T Γ) (τ : Δ ≤ Γ) → V⦅ x w[ τ ]ᵛ ⦆ ≡ V⦅ x ⦆ ∘′ Ar τ
wk-evalv x id≤      = refl
wk-evalv x (weak τ) rewrite wk-evalv x τ = refl
wk-evalv vz (lift τ) = refl
wk-evalv (vs x) (lift τ) rewrite wk-evalv x τ = refl

wk-eval : ∀{Γ Δ T} (t : Tm Γ T) (τ : Δ ≤ Γ) → E⦅ t w[ τ ]ᵉ ⦆ ≡ E⦅ t ⦆ ∘′ Ar τ
wk-eval (var x) τ = wk-evalv x τ
wk-eval (abs t) τ rewrite wk-eval t (lift τ) = refl
wk-eval (app t u) τ rewrite wk-eval t τ | wk-eval u τ = refl

{-# REWRITE wk-eval #-}

-- A syntactic logical relation:
-- f is in the logical relation if it is the image of a t under evaluation.

TmImg : ∀ Γ T (f : Fun Γ T) → Set
TmImg Γ T f = ∃ λ (t : Tm Γ T) → E⦅ t ⦆ ≡ f

TmKLP : STLC-KLP
TmKLP .STLC-KLP.B⟦_⟧ b Γ f           = TmImg Γ (base b) f
TmKLP .STLC-KLP.monB b τ (t , refl)  = t w[ τ ]ᵉ , wk-eval t τ

-- TmKLP .STLC-KLP.monB b {Γ} {Δ} τ {f} (t , ⦅t⦆≡f) =
--   t w[ τ ]ᵉ , subst (λ z → _ ≡ z ∘′ Ar τ) ⦅t⦆≡f (wk-eval t τ)

-- Reflection / reification

module _ (open STLC-KLP-Ext TmKLP) where
  mutual

    reflect : ∀{Γ} T (t : Tm Γ T) → T⟦ T ⟧ Γ E⦅ t ⦆
    reflect (base b) t = t , refl
    reflect {Γ} (U ⇒ T) t {Δ} τ {d} ⟦d⟧ with reify U ⟦d⟧
    reflect {Γ} (U ⇒ T) t {Δ} τ {d} ⟦d⟧ | u , refl = reflect T (app (t w[ τ ]ᵉ) u) -- REWRITE wk-eval

    reify : ∀{Γ} T {f : Fun Γ T} (⟦f⟧ : T⟦ T ⟧ Γ f) → TmImg Γ T f
    reify (base b) ⟦f⟧ = ⟦f⟧
    reify (U ⇒ T) ⟦f⟧ with reify T (⟦f⟧ (weak id≤) {proj₂} (reflect U (var vz)))
    ... | t , ⦅t⦆≡uncurryf = abs t , cong curry ⦅t⦆≡uncurryf

-- Soundness: every STLC-definable function is the image of a term.

sound : ∀{Γ T f} (def : STLC-definable Γ T f) → TmImg Γ T f
sound def = reify _ (def TmKLP)

-- Fundamental lemma of LR.

module Fund (P : STLC-KLP) (open STLC-KLP-Ext P) where

  -- Extension of KLP to contexts

  C⟦_⟧ : (Γ Δ : Cxt) (ρ : CFun Δ Γ) → Set
  C⟦ ε ⟧ Δ !Δ = ⊤
  C⟦ Γ ▷ U ⟧ Δ ρ = C⟦ Γ ⟧ Δ (proj₁ ∘′ ρ) × T⟦ U ⟧ Δ (proj₂ ∘′ ρ)

  -- Monotonicity of the context-KLP.
  -- This is the only place where we need monotonicity of KLPs.

  monC : ∀ Γ {Δ Φ} (τ : Φ ≤ Δ) {ρ : CFun Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ Δ ρ) → C⟦ Γ ⟧ Φ (ρ ∘′ Ar τ)
  monC ε τ ⟦ρ⟧ = _
  monC (Γ ▷ U) τ ⟦ρ⟧ = monC Γ τ (proj₁ ⟦ρ⟧) , monT U τ (proj₂ ⟦ρ⟧)

  -- Fundamental theorem

  fundv : ∀{Γ Δ T} (x : Var T Γ) {ρ : CFun Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ Δ ρ) → T⟦ T ⟧ Δ (V⦅ x ⦆ ∘′ ρ)
  fundv vz     ⟦ρ⟧ = proj₂ ⟦ρ⟧
  fundv (vs x) ⟦ρ⟧ = fundv x (proj₁ ⟦ρ⟧)

  fund : ∀{Γ Δ T} (t : Tm Γ T) {ρ : CFun Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ Δ ρ) → T⟦ T ⟧ Δ (E⦅ t ⦆ ∘′ ρ)
  fund (var x)   ⟦ρ⟧       =  fundv x ⟦ρ⟧
  fund (abs t)   ⟦ρ⟧ τ ⟦d⟧  =  fund t (monC _ τ ⟦ρ⟧ , ⟦d⟧)  -- Monotonicity used here!
  fund (app t u) ⟦ρ⟧       =  fund t ⟦ρ⟧ id≤ (fund u ⟦ρ⟧)

  -- -- Identity environment does not always exist!
  -- mutual
  --   wkC : ∀{Γ Δ} (τ : Δ ≤ Γ) → C⟦ Γ ⟧ Δ (Ar τ)
  --   wkC id≤ = idC _
  --   wkC (weak τ) = {!!}
  --   wkC (lift τ) = {!!}

  --   idC : ∀ Γ → C⟦ Γ ⟧ Γ id
  --   idC ε = _
  --   idC (Γ ▷ U) = monC _ (weak id≤) (idC Γ) , {! fundv vz {proj₁} (wkC {Γ} (weak id≤)) !}
  --   -- idC (Γ ▷ U) = monC _ (weak id≤) (idC Γ) , {!wkC (weak id≤)!} -- fundv vz (idC (Γ ▷ U))

-- complete : ∀{Γ T} (t : Tm Γ T) → STLC-definable Γ T E⦅ t ⦆
-- complete t P = {!!}

-- Completeness: Every closed term evaluates to a STLC-definable function.

complete⁰ : ∀{T} (t : Tm ε T) → STLC-definable ε T E⦅ t ⦆
complete⁰ t P = fund {Δ = ε} t {id} _
  where open Fund P

  -- fund (app t u) {ρ} ⟦ρ⟧ = fund t ⟦ρ⟧ id≤ {E⦅ u ⦆ ∘′ ρ} (fund u ⟦ρ⟧)
-- -}
-- -}
-- -}
-- -}
-- -}
