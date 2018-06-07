-- (Meta-level) functions and their characterization by Kripke predicates

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Library
import SimpleTypes

module STLCDefinable
  (Base : Set)  (B⦅_⦆ : Base → Set) (open SimpleTypes Base B⦅_⦆)
  (Const : Set) (ty : Const → Ty) (c⦅_⦆ : (c : Const) → T⦅ ty c ⦆)
  where

-- A Kripke logical predicate is uniquely determined by its definition at base type

record STLC-KLP-Base : Set₁ where
  field
    B⟦_⟧  : (b : Base) → KPred B⦅ b ⦆
    monB  : (b : Base) → mon B⟦ b ⟧

-- Kripke logical predicate over the world of context extensions

module STLC-KLP-Ext (P : STLC-KLP-Base) (open STLC-KLP-Base P) where

  T⟦_⟧ : (T : Ty) → KPred T⦅ T ⦆
  T⟦ base b ⟧ = B⟦ b ⟧
  T⟦ U ⇒ T ⟧ Γ f =
    ∀{Δ} (τ : Δ ≤ Γ) {d : Fun Δ U}
    →  (⟦d⟧ : T⟦ U ⟧ Δ d)
    →  T⟦ T ⟧ Δ (kapp f (R⦅ τ ⦆) d)

  monT : ∀ T → mon T⟦ T ⟧
  monT (base b) = monB b
  monT (U ⇒ T) {Γ} {Δ} τ {f} ⟦f⟧ {Φ} τ′ {d} ⟦d⟧ = ⟦f⟧ (τ ∙ τ′) {d} ⟦d⟧  -- needs REWRITE ar-comp

-- A Kripke logical predicate needs to satisfy all constants
record STLC-KLP : Set₁ where
  field
    klp-base : STLC-KLP-Base
  open STLC-KLP-Base klp-base public
  open STLC-KLP-Ext klp-base public
  field
    satC : (c : Const) → T⟦ ty c ⟧ ε (λ _ → c⦅ c ⦆)

-- A function is STLC-definable if it satisfies all STLC-KLPs.
-- This is a "big" proposition.
-- But it is purely semantic, independent from any syntactic definitions.

STLC-definable : ∀ Γ T (f : Fun Γ T) → Set₁
STLC-definable Γ T f = ∀ (P : STLC-KLP) (open STLC-KLP P) → T⟦ T ⟧ Γ f

-- In the following we prove that a function is STLC-definable iff
-- it is the evaluation of a STLC term.

-- STLC

data Var (T : Ty) : (Γ : Cxt) → Set where
  vz : ∀{Γ} → Var T (Γ ▷ T)
  vs : ∀{Γ U} (x : Var T Γ) → Var T (Γ ▷ U)

data Tm (Γ : Cxt) : (T : Ty) → Set where
  con : (c : Const) → Tm Γ (ty c)
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
con c   w[ τ ]ᵉ = con c
var x   w[ τ ]ᵉ = var (x w[ τ ]ᵛ)
abs t   w[ τ ]ᵉ = abs (t w[ lift τ ]ᵉ)
app t u w[ τ ]ᵉ = app (t w[ τ ]ᵉ) (u w[ τ ]ᵉ)

-- Evaluation of variables and expressions

V⦅_⦆ : ∀{Γ T} → Var T Γ → Fun Γ T
V⦅ vz ⦆   = proj₂
V⦅ vs x ⦆ = V⦅ x ⦆ ∘′ proj₁

E⦅_⦆ : ∀{Γ T} → Tm Γ T → Fun Γ T
E⦅ con c ⦆ _ = c⦅ c ⦆
E⦅ var x ⦆   = V⦅ x ⦆
E⦅ abs t ⦆   = curry E⦅ t ⦆
E⦅ app t u ⦆ = apply E⦅ t ⦆ E⦅ u ⦆

-- Evaluation of a term t weakened by τ
-- is the evaluation of t postcomposed with the action of τ.

wk-evalv : ∀{Γ Δ T} (x : Var T Γ) (τ : Δ ≤ Γ) → V⦅ x w[ τ ]ᵛ ⦆ ≡ V⦅ x ⦆ ∘′ R⦅ τ ⦆
wk-evalv x id≤      = refl
wk-evalv x (weak τ) rewrite wk-evalv x τ = refl
wk-evalv vz (lift τ) = refl
wk-evalv (vs x) (lift τ) rewrite wk-evalv x τ = refl

wk-eval : ∀{Γ Δ T} (t : Tm Γ T) (τ : Δ ≤ Γ) → E⦅ t w[ τ ]ᵉ ⦆ ≡ E⦅ t ⦆ ∘′ R⦅ τ ⦆
wk-eval (con c) τ = refl
wk-eval (var x) τ = wk-evalv x τ
wk-eval (abs t) τ rewrite wk-eval t (lift τ) = refl
wk-eval (app t u) τ rewrite wk-eval t τ | wk-eval u τ = refl

{-# REWRITE wk-eval #-}

-- A syntactic logical relation:
-- f is in the logical relation if it is the image of a t under evaluation.

TmImg : ∀ Γ T (f : Fun Γ T) → Set
TmImg Γ T f = ∃ λ (t : Tm Γ T) → E⦅ t ⦆ ≡ f

TmKLP-Base : STLC-KLP-Base
TmKLP-Base .STLC-KLP-Base.B⟦_⟧ b Γ f           = TmImg Γ (base b) f
TmKLP-Base .STLC-KLP-Base.monB b τ (t , refl)  = t w[ τ ]ᵉ , wk-eval t τ

-- Reflection / reification

module _ (open STLC-KLP-Ext TmKLP-Base) where
  mutual

    reflect : ∀{Γ} T (t : Tm Γ T) → T⟦ T ⟧ Γ E⦅ t ⦆
    reflect (base b) t = t , refl
    reflect (U ⇒ T) t τ ⟦d⟧ with reify U ⟦d⟧
    reflect (U ⇒ T) t τ ⟦d⟧ | u , refl = reflect T (app (t w[ τ ]ᵉ) u) -- REWRITE wk-eval

    reify : ∀{Γ} T {f : Fun Γ T} (⟦f⟧ : T⟦ T ⟧ Γ f) → TmImg Γ T f
    reify (base b) ⟦f⟧ = ⟦f⟧
    reify (U ⇒ T) ⟦f⟧ with reify T (⟦f⟧ (weak id≤) {proj₂} (reflect U (var vz)))
    ... | t , ⦅t⦆≡uncurryf = abs t , cong curry ⦅t⦆≡uncurryf

TmKLP : STLC-KLP
TmKLP .STLC-KLP.klp-base = TmKLP-Base
TmKLP .STLC-KLP.satC c = reflect (ty c) (con c)

-- Soundness: every STLC-definable function is the image of a term.

sound : ∀{Γ T f} (def : STLC-definable Γ T f) → TmImg Γ T f
sound def = reify _ (def TmKLP)

-- Fundamental lemma of LR.

module Fund (P : STLC-KLP) (open STLC-KLP P) where

  -- Extension of KLP to contexts

  C⟦_⟧ : (Γ Δ : Cxt) (ρ : CFun Δ Γ) → Set
  C⟦ ε ⟧ Δ !Δ = ⊤
  C⟦ Γ ▷ U ⟧ Δ ρ = C⟦ Γ ⟧ Δ (proj₁ ∘′ ρ) × T⟦ U ⟧ Δ (proj₂ ∘′ ρ)

  -- Monotonicity of the context-KLP.
  -- This is the only place where we need monotonicity of KLPs.

  monC : ∀ Γ {Δ Φ} (τ : Φ ≤ Δ) {ρ : CFun Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ Δ ρ) → C⟦ Γ ⟧ Φ (ρ ∘′ R⦅ τ ⦆)
  monC ε τ ⟦ρ⟧ = _
  monC (Γ ▷ U) τ ⟦ρ⟧ = monC Γ τ (proj₁ ⟦ρ⟧) , monT U τ (proj₂ ⟦ρ⟧)

  -- Fundamental theorem

  fundv : ∀{Γ Δ T} (x : Var T Γ) {ρ : CFun Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ Δ ρ) → T⟦ T ⟧ Δ (V⦅ x ⦆ ∘′ ρ)
  fundv vz     ⟦ρ⟧ = proj₂ ⟦ρ⟧
  fundv (vs x) ⟦ρ⟧ = fundv x (proj₁ ⟦ρ⟧)

  fund : ∀{Γ Δ T} (t : Tm Γ T) {ρ : CFun Δ Γ} (⟦ρ⟧ : C⟦ Γ ⟧ Δ ρ) → T⟦ T ⟧ Δ (E⦅ t ⦆ ∘′ ρ)
  fund (con c)   ⟦ρ⟧       =  monT (ty c) (≤ε _) (satC c)
  fund (var x)   ⟦ρ⟧       =  fundv x ⟦ρ⟧
  fund (abs t)   ⟦ρ⟧ τ ⟦d⟧  =  fund t (monC _ τ ⟦ρ⟧ , ⟦d⟧)  -- Monotonicity used here!
  fund (app t u) ⟦ρ⟧       =  fund t ⟦ρ⟧ id≤ (fund u ⟦ρ⟧)

-- complete : ∀{Γ T} (t : Tm Γ T) → STLC-definable Γ T E⦅ t ⦆
-- complete t P = {!!}

-- Completeness: Every closed term evaluates to a STLC-definable function.
-- (Does not directly scale to open terms since identity environment does not always exist!)

complete⁰ : ∀{T} (t : Tm ε T) → STLC-definable ε T E⦅ t ⦆
complete⁰ t P = fund {Δ = ε} t {id} _
  where open Fund P

-- -}
-- -}
-- -}
-- -}
