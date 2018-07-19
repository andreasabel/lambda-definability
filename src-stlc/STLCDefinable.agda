-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, May/June 2018

-- 2. Simply-typed lambda calculus (STLC) definability

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Library
import SimpleTypes

-- The notion of Kripke predicate is parametrized by base types
-- and simply-typed constants and their interpretation.

module STLCDefinable
  (Base : Set)  (B⦅_⦆ : Base → Set) (open SimpleTypes Base B⦅_⦆)
  (Const : Set) (ty : Const → Ty) (c⦅_⦆ : (c : Const) → T⦅ ty c ⦆)
  where

-- A Kripke logical predicate (KLP) is uniquely determined
-- by its definition at base type.

record STLC-KLP-Base : Set₁ where
  field
    B⟦_⟧  : (b : Base) → KPred B⦅ b ⦆
    monB  : (b : Base) → Mon B⟦ b ⟧
    ⟦N⟧ : KPred ℕ
    monN : Mon ⟦N⟧


rec : ∀{A : Set} → A → (ℕ → A → A) → ℕ → A
rec z s zero = z
rec z s (suc n) = s n (rec z s n)

-- Kripke logical predicate over the world of context embeddings.

module STLC-KLP-Ext (P : STLC-KLP-Base) (open STLC-KLP-Base P) where

  -- Monotonicity is built into the definition of a Kripke predicate
  -- at function type.

  T⟦_⟧ : (T : Ty) → KPred T⦅ T ⦆
  T⟦ N ⟧ = ⟦N⟧
  T⟦ base b ⟧ = B⟦ b ⟧
  T⟦ U ⇒ T ⟧ Γ f =
    ∀{Δ} (τ : Δ ≤ Γ) {d : Fun Δ U}
    →  (⟦d⟧ : T⟦ U ⟧ Δ d)
    →  T⟦ T ⟧ Δ (apply (f ∘′ R⦅ τ ⦆) d)
  T⟦ U ×̂ T ⟧ Γ p = T⟦ U ⟧ Γ (proj₁ ∘′ p) × T⟦ T ⟧ Γ (proj₂ ∘′ p)

  -- Thus, the monotonicity proof is a simple case distinction
  -- between base types and function types (no induction).

  monT : ∀ T → Mon T⟦ T ⟧
  monT N = monN
  monT (base b) = monB b
  monT (U ⇒ T) τ ⟦f⟧ τ′ ⟦d⟧ = ⟦f⟧ (τ ∙ τ′) ⟦d⟧  -- needs REWRITE ar-comp

-- A Kripke logical predicate needs to satisfy all constants.
  monT (U ×̂ T) {Γ} {Δ} τ {f} ( ⟦u⟧ , ⟦t⟧ ) = monT U τ ⟦u⟧ , monT T τ ⟦t⟧

record STLC-KLP : Set₁ where
  field
    klp-base : STLC-KLP-Base
  open STLC-KLP-Base klp-base public
  open STLC-KLP-Ext klp-base public
  field
    satC   : (c : Const) → T⟦ ty c ⟧ ε (λ _ → c⦅ c ⦆)
    satZ   : T⟦ N ⟧ ε (λ _ → 0)
    satS   : ∀ {Γ} {⦅t⦆ : Fun Γ N}
             → T⟦ N ⟧ Γ ⦅t⦆
             → T⟦ N ⟧ Γ (suc ∘′ ⦅t⦆)
    satREC : ∀ {T Γ} {⦅z⦆ : Fun Γ T} {⦅s⦆ : Fun Γ (N ⇒ (T ⇒ T))} {⦅n⦆ : Fun Γ N}
             → (⟦z⟧ : T⟦ T ⟧ Γ ⦅z⦆)
             → (⟦s⟧ : T⟦ N ⇒ (T ⇒ T) ⟧ Γ ⦅s⦆)
             → (⟦n⟧ : T⟦ N ⟧ Γ ⦅n⦆)
             → T⟦ T ⟧ Γ (λ γ → rec (⦅z⦆ γ) (⦅s⦆ γ) (⦅n⦆ γ))

-- A function is STLC-definable if it satisfies all STLC-KLPs.
-- This is a "big" proposition.
-- But it is purely semantic, independent from any syntactic definitions.

STLC-definable : ∀ Γ T (f : Fun Γ T) → Set₁
STLC-definable Γ T f = ∀ (P : STLC-KLP) (open STLC-KLP P) → T⟦ T ⟧ Γ f

-- In the following we prove that a function is STLC-definable iff
-- it is the evaluation of a STLC term.

-- Syntax of STLC (intrinsically typed).

-- Well-typed variables: (de Bruijn) indices into the contexts.

data Var (T : Ty) : (Γ : Cxt) → Set where
  vz : ∀{Γ} → Var T (Γ ▷ T)
  vs : ∀{Γ U} (x : Var T Γ) → Var T (Γ ▷ U)

-- Well-typed terms over the set Const of constants.

data Tm (Γ : Cxt) : (T : Ty) → Set where
  con  : (c : Const) → Tm Γ (ty c)
  var  : ∀{T}   (x : Var T Γ) → Tm Γ T
  abs  : ∀{U T} (t : Tm (Γ ▷ U) T) → Tm Γ (U ⇒ T)
  app  : ∀{U T} (t : Tm Γ (U ⇒ T)) (u : Tm Γ U) → Tm Γ T
  pair : ∀{U T} (u : Tm Γ U) (t : Tm Γ T) → Tm Γ (U ×̂ T)
  fst  : ∀{U T} (t : Tm Γ (U ×̂ T)) → Tm Γ U
  snd  : ∀{U T} (t : Tm Γ (U ×̂ T)) → Tm Γ T
  zero : Tm Γ N
  suc : Tm Γ N → Tm Γ N
  recN : ∀{T} → (z : Tm Γ T) → (s : Tm Γ (N ⇒ (T ⇒ T))) → (n : Tm Γ N) → Tm Γ T

-- Weakening with an OPE.

_w[_]ᵛ : ∀{Γ Δ T} (x : Var T Γ) (τ : Δ ≤ Γ) → Var T Δ
x    w[ id≤    ]ᵛ = x
x    w[ weak τ ]ᵛ = vs (x w[ τ ]ᵛ)
vz   w[ lift τ ]ᵛ = vz
vs x w[ lift τ ]ᵛ = vs (x w[ τ ]ᵛ)

_w[_]ᵉ : ∀{Γ Δ T} (t : Tm Γ T) (τ : Δ ≤ Γ) → Tm Δ T
con c    w[ τ ]ᵉ = con c
var x    w[ τ ]ᵉ = var (x w[ τ ]ᵛ)
abs t    w[ τ ]ᵉ = abs (t w[ lift τ ]ᵉ)
app t u  w[ τ ]ᵉ = app (t w[ τ ]ᵉ) (u w[ τ ]ᵉ)
pair u t w[ τ ]ᵉ = pair (u w[ τ ]ᵉ) (t w[ τ ]ᵉ)
fst t    w[ τ ]ᵉ = fst (t w[ τ ]ᵉ)
snd t    w[ τ ]ᵉ = snd (t w[ τ ]ᵉ)
zero     w[ τ ]ᵉ = zero
suc t      w[ τ ]ᵉ = suc (t w[ τ ]ᵉ)
recN z s n w[ τ ]ᵉ = recN (z w[ τ ]ᵉ) (s w[ τ ]ᵉ) (n w[ τ ]ᵉ)

-- Evaluation of variables and expressions

V⦅_⦆ : ∀{Γ T} → Var T Γ → Fun Γ T
V⦅ vz ⦆   = proj₂
V⦅ vs x ⦆ = V⦅ x ⦆ ∘′ proj₁

E⦅_⦆ : ∀{Γ T} → Tm Γ T → Fun Γ T
E⦅ con c ⦆ _  = c⦅ c ⦆
E⦅ var x ⦆    = V⦅ x ⦆
E⦅ abs t ⦆    = curry E⦅ t ⦆
E⦅ app t u ⦆  = apply E⦅ t ⦆ E⦅ u ⦆
E⦅ pair u t ⦆ = < E⦅ u ⦆ , E⦅ t ⦆ >
E⦅ fst t ⦆    = proj₁ ∘ E⦅ t ⦆
E⦅ snd t ⦆    = proj₂ ∘ E⦅ t ⦆
E⦅ zero ⦆     = λ Γ → 0
E⦅ suc t ⦆      = suc ∘′ E⦅ t ⦆
E⦅ recN z s n ⦆ γ = rec (E⦅ z ⦆ γ) (E⦅ s ⦆ γ) (E⦅ n ⦆ γ)

-- Evaluation of a term t weakened by τ
-- is the evaluation of t postcomposed with the action of τ.

wk-evalv : ∀{Γ Δ T} (x : Var T Γ) (τ : Δ ≤ Γ) → V⦅ x w[ τ ]ᵛ ⦆ ≡ V⦅ x ⦆ ∘′ R⦅ τ ⦆
wk-evalv x      id≤      = refl
wk-evalv x      (weak τ) rewrite wk-evalv x τ = refl
wk-evalv vz     (lift τ) = refl
wk-evalv (vs x) (lift τ) rewrite wk-evalv x τ = refl

wk-eval : ∀{Γ Δ T} (t : Tm Γ T) (τ : Δ ≤ Γ) → E⦅ t w[ τ ]ᵉ ⦆ ≡ E⦅ t ⦆ ∘′ R⦅ τ ⦆
wk-eval (con c)    τ = refl
wk-eval (var x)    τ = wk-evalv x τ
wk-eval (abs t)    τ rewrite wk-eval t (lift τ) = refl
wk-eval (app t u)  τ rewrite wk-eval t τ | wk-eval u τ = refl
wk-eval (pair u t) τ rewrite wk-eval u τ | wk-eval t τ = refl
wk-eval (fst t)    τ rewrite wk-eval t τ = refl
wk-eval (snd t)    τ rewrite wk-eval t τ = refl
wk-eval zero       τ = refl
wk-eval (suc t)      τ rewrite wk-eval t τ = refl
wk-eval (recN z s n) τ rewrite wk-eval z τ | wk-eval s τ | wk-eval n τ = refl

{-# REWRITE wk-eval #-}

-- A syntactic logical relation:
-- f is in the logical relation if it is the image of a t under evaluation.

TmImg : ∀ Γ T (f : Fun Γ T) → Set
TmImg Γ T f = ∃ λ (t : Tm Γ T) → E⦅ t ⦆ ≡ f

TmKLP-Base : STLC-KLP-Base
TmKLP-Base .STLC-KLP-Base.B⟦_⟧ b Γ f           = TmImg Γ (base b) f
TmKLP-Base .STLC-KLP-Base.monB b τ (t , refl)  = t w[ τ ]ᵉ , wk-eval t τ
TmKLP-Base .STLC-KLP-Base.⟦N⟧ Γ f = TmImg Γ N f
TmKLP-Base .STLC-KLP-Base.monN τ (t , refl) = t w[ τ ]ᵉ , wk-eval t τ

-- Reflection / reification

-- We can reflect terms into the Kripke model by evaluation.
-- We can reify a term from an element of the Kripke model.

-- These two lemmata are proven simultaneously by induction on the type.

module _ (open STLC-KLP-Ext TmKLP-Base) where
  mutual

    reflect : ∀{Γ} T (t : Tm Γ T) → T⟦ T ⟧ Γ E⦅ t ⦆
    reflect (base b) t = t , refl
    reflect (U ⇒ T) t τ ⟦d⟧ with reify U ⟦d⟧
    reflect (U ⇒ T) t τ ⟦d⟧ | u , refl = reflect T (app (t w[ τ ]ᵉ) u) -- REWRITE wk-eval
    reflect (U ×̂ T) t = reflect U (fst t) , reflect T (snd t)
    reflect N t = t , refl

    reify : ∀{Γ} T {f : Fun Γ T} (⟦f⟧ : T⟦ T ⟧ Γ f) → TmImg Γ T f
    reify (base b) ⟦f⟧ = ⟦f⟧
    reify (U ⇒ T) ⟦f⟧ with reify T (⟦f⟧ (weak id≤) {proj₂} (reflect U (var vz)))
    ... | t , ⦅t⦆≡uncurryf = abs t , cong curry ⦅t⦆≡uncurryf
    reify (U ×̂ T) ⟦f⟧ with reify U (proj₁ ⟦f⟧) | reify T (proj₂ ⟦f⟧)
    ... | u , ⦅u⦆≡proj₁∘f | t , ⦅t⦆≡proj₂∘f = pair u t , cong₂ <_,_> ⦅u⦆≡proj₁∘f ⦅t⦆≡proj₂∘f
    reify N ⟦f⟧ = ⟦f⟧

-- Reflection witnesses that the constants satisfy the corresponding Kripke predicate.

module _ (open STLC-KLP-Ext TmKLP-Base) where
  TmKLP : STLC-KLP
  TmKLP .STLC-KLP.klp-base = TmKLP-Base
  TmKLP .STLC-KLP.satC c = reflect (ty c) (con c)
  TmKLP .STLC-KLP.satZ = reflect N zero
  TmKLP .STLC-KLP.satS ⟦t⟧ with reify N ⟦t⟧
  ... | t , refl = reflect N (suc t)
  TmKLP .STLC-KLP.satREC {T = T} {⦅s⦆ = ⦅s⦆} ⟦z⟧ ⟦s⟧ ⟦n⟧
      with reify T ⟦z⟧ | reify (N ⇒ (T ⇒ T)) {⦅s⦆} ⟦s⟧ | reify N ⟦n⟧
  ... | z , refl | s , refl | n , refl = reflect T (recN z s n)

-- Soundness: every STLC-definable function is the image of a term.

sound : ∀{Γ T f} (def : STLC-definable Γ T f) → TmImg Γ T f
sound def = reify _ (def TmKLP)

-- Fundamental lemma of logical relations.

module Fund (P : STLC-KLP) (open STLC-KLP P) where

  -- Pointwise extension of KLP to contexts.

  C⟦_⟧ : (Γ Δ : Cxt) (ρ : CFun Δ Γ) → Set
  C⟦ ε ⟧     Δ !Δ = ⊤
  C⟦ Γ ▷ U ⟧ Δ ρ = C⟦ Γ ⟧ Δ (proj₁ ∘′ ρ) × T⟦ U ⟧ Δ (proj₂ ∘′ ρ)

  -- Monotonicity of the context-KLP.
  -- This is the only place where we need monotonicity of KLPs.

  monC : ∀ Γ {Δ Φ} (τ : Φ ≤ Δ) {ρ : CFun Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ Δ ρ) → C⟦ Γ ⟧ Φ (ρ ∘′ R⦅ τ ⦆)
  monC ε       τ ⟦ρ⟧ = _
  monC (Γ ▷ U) τ ⟦ρ⟧ = monC Γ τ (proj₁ ⟦ρ⟧) , monT U τ (proj₂ ⟦ρ⟧)

  -- Fundamental theorem.

  -- Proves that the image of any well-typed term satisfies every Kripke predicate
  -- (not just the syntactic one as in reflection).

  -- Needs to be generalized to include environments ρ.
  -- Could even be generalized to Kripke predicates over any world type
  -- (not just contexts and embeddings).

  fundv : ∀{Γ Δ T} (x : Var T Γ) {ρ : CFun Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ Δ ρ) → T⟦ T ⟧ Δ (V⦅ x ⦆ ∘′ ρ)
  fundv vz     ⟦ρ⟧ = proj₂ ⟦ρ⟧
  fundv (vs x) ⟦ρ⟧ = fundv x (proj₁ ⟦ρ⟧)

  fund : ∀{Γ Δ T} (t : Tm Γ T) {ρ : CFun Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ Δ ρ) → T⟦ T ⟧ Δ (E⦅ t ⦆ ∘′ ρ)
  fund (con c)    ⟦ρ⟧       = monT (ty c) (≤ε _) (satC c)
  fund (var x)    ⟦ρ⟧       = fundv x ⟦ρ⟧
  fund (abs t)    ⟦ρ⟧ τ ⟦d⟧ = fund t (monC _ τ ⟦ρ⟧ , ⟦d⟧)  -- Monotonicity used here!
  fund (app t u)  ⟦ρ⟧       = fund t ⟦ρ⟧ id≤ (fund u ⟦ρ⟧)
  fund (pair u t) ⟦ρ⟧       = fund u ⟦ρ⟧ , fund t ⟦ρ⟧
  fund (fst t)    ⟦ρ⟧       = proj₁ (fund t ⟦ρ⟧)
  fund (snd t)    ⟦ρ⟧       = proj₂ (fund t ⟦ρ⟧)
  fund zero       ⟦ρ⟧       = monT N (≤ε _) satZ
  fund (suc t) {ρ}  ⟦ρ⟧       = satS (fund t ⟦ρ⟧)
  fund (recN {T} z s n) ⟦ρ⟧  = satREC {T} (fund z ⟦ρ⟧) (fund s ⟦ρ⟧) (fund n ⟦ρ⟧)

-- Completeness: Every closed term evaluates to a STLC-definable function.
-- (Does not directly scale to open terms since identity environment does not always exist!)

complete⁰ : ∀{T} (t : Tm ε T) → STLC-definable ε T E⦅ t ⦆
complete⁰ t P = fund {Δ = ε} t {id} _
  where open Fund P

-- Q.E.D.
