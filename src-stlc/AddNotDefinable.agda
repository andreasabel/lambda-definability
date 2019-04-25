-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, 25 April 2019

-- 4c. Using Kripke predicates to refute STLC-definability of addition.

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Data.Nat.Base as ℕ using (ℕ; zero; suc; pred; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (suc-injective; ≤-trans; n≮n; m≤m+n; n≤m+n; ≤-stepsˡ; ≤-stepsʳ; m+n≤o⇒n≤o; +-monoˡ-≤; ≤⇒pred≤; ≰⇒≮; i+1+j≰i)

open import Library

import SimpleTypes
import STLCDefinable

module AddNotDefinable where

pred-< : ∀ {m n} → m < n → pred m < n
pred-< {zero}  p = p
pred-< {suc m} p = m+n≤o⇒n≤o 1 p

-- We consider STLC with a base type "nat" with constants
-- "zero", "suc" and "case".

data Base : Set where
  nat : Base

B⦅_⦆ : Base → Set
B⦅ nat ⦆ = ℕ

open SimpleTypes Base B⦅_⦆

data Const : Set where
  zero : Const
  suc  : Const
  case : Ty → Const

pattern tnat = base nat

ty : Const → Ty
ty zero    = tnat
ty suc     = tnat ⇒ tnat
ty (case t) = tnat ×̂ t ×̂ (tnat ⇒ t) ⇒ t

caseN : ∀{A : Set} (n : ℕ) (z : A) (s : ℕ → A) → A
caseN zero    z s = z
caseN (suc n) z s = s n

c⦅_⦆ : (c : Const) → T⦅ ty c ⦆
c⦅ zero   ⦆ = zero
c⦅ suc    ⦆ n = suc n
c⦅ case t ⦆ (zero  , z , s) = z
c⦅ case t ⦆ (suc n , z , s) = s n

-- We now prove that addition is not STLC definable
-- by constructing a countermodel.

open STLCDefinable Base B⦅_⦆ Const ty c⦅_⦆

-- The model is functions bounded by constant plus possible
-- the value of one variable.

data BoundedBy Γ γ n k : Set where
  bconst : (p : n < k)                            → BoundedBy Γ γ n k
  bvar   : (x : Var tnat Γ) (p : n < k + V⦅ x ⦆ γ) → BoundedBy Γ γ n k

record Bounded Γ (f : Fun Γ tnat) : Set where
  constructor bounded
  field
    k : ℕ
    h : ∀ γ → BoundedBy Γ γ (f γ) k

-- Addition is not bounded!

add : Fun ((ε ▷ tnat) ▷ tnat) tnat
add ((_ , m) , n) = m + n

addNotBounded : ¬ Bounded _ add
addNotBounded (bounded k h) =
  case h ((_ , suc k) , suc k) of λ where
    (bconst       p) → i+1+j≰i _ (m+n≤o⇒n≤o 2 p) -- p : suc (k + suc k) < k
    (bvar vz      p) → ≰⇒≮ (n≮n _) p             -- p : suc (k + suc k) < k + suc k
    (bvar (vs vz) p) → ≰⇒≮ (n≮n _) p             -- p : suc (k + suc k) < k + suc k

-- BoundedBy is monotone.

BoundedBy-≤ : ∀{Γ γ n k l} → k ℕ.≤ l → BoundedBy Γ γ n k → BoundedBy Γ γ n l
BoundedBy-≤ p (bconst b) = bconst (≤-trans b p)
BoundedBy-≤ p (bvar x b) = bvar x (≤-trans b (+-monoˡ-≤ _ p))

-- Weakening boundedness.

wkBounded : ∀ {Γ Δ} {f : C⦅ Γ ⦆ → ℕ} →
            Bounded Γ f → (τ : Δ ≤ Γ) → Bounded Δ (f ∘ R⦅ τ ⦆)
wkBounded (bounded k h) τ = bounded k λ γ →
  case h (R⦅ τ ⦆ γ) of λ where
    (bconst p) → bconst p
    (bvar x p) → bvar (wkVar x τ) p

-- Kripke model

NN-Base : STLC-KLP-Base
NN-Base .STLCDefinable.STLC-KLP-Base.B⟦_⟧  nat Γ f = Bounded Γ f
NN-Base .STLCDefinable.STLC-KLP-Base.monB nat τ b = wkBounded b τ

open STLC-KLP-Ext NN-Base

-- zero and suc are bounded.

zeroBounded : ∀{Γ} → Bounded Γ (λ _ → zero)
zeroBounded = bounded 1 λ γ → bconst (s≤s z≤n)

sucBounded : ∀{Γ f} → Bounded Γ f → Bounded Γ (suc ∘ f)
sucBounded (bounded k h) = bounded (suc k) λ γ →
  case h γ of λ where
    (bconst p) → bconst (s≤s p)
    (bvar x p) → bvar x (s≤s p)

⟦pred⟧ : ∀{Γ f} → Bounded Γ f → Bounded Γ (pred ∘ f)
⟦pred⟧ (bounded k h) = bounded k λ γ →
   case h γ of λ where
     (bconst (s≤s p)) → bconst (s≤s (≤⇒pred≤ p))
     (bvar x p) → bvar x (pred-< p)  -- m < n → pred m < n

caseSat' : ∀ {Γ} c  {n : Fun Γ tnat} {z : Fun Γ c} {s : Fun Γ (tnat ⇒ c)} →
      (⟦n⟧ : T⟦ tnat     ⟧ Γ n) →
      (⟦z⟧ : T⟦ c        ⟧ Γ z) →
      (⟦s⟧ : T⟦ tnat ⇒ c ⟧ Γ s) →
      -- T⟦ c        ⟧ Γ (λ γ → caseN (n γ) (z γ) (s γ))
      T⟦ c        ⟧ Γ (c⦅ case c ⦆ ∘ λ γ → (n γ , z γ , s γ))
caseSat' tnat {n} {z} {s} ⟦n⟧ (bounded kz hz) ⟦s⟧ with ⟦s⟧ id≤ (⟦pred⟧ ⟦n⟧)
... | bounded ks hs = bounded (kz + ks) λ γ → aux γ (n γ) (hz γ) (hs γ)
  where
  aux : ∀ γ m
      → BoundedBy _ γ (z γ) kz
      → BoundedBy _ γ (s γ (pred m)) ks
      → BoundedBy _ γ (c⦅ case tnat ⦆ (m , z γ , s γ)) (kz + ks)
  aux γ zero    hz hs = BoundedBy-≤ (m≤m+n _ _) hz
  aux γ (suc m) hz hs = BoundedBy-≤ (n≤m+n _ _) hs
caseSat' (a ⇒ b) ⟦n⟧ ⟦z⟧ ⟦s⟧ τ ⟦d⟧ = {! caseSat' b {! monT _ τ ⟦n⟧ !} {!!} {!!} !}  -- need c⦅ case (a ⇒ b) ⦆ to reduce!
caseSat' (a ×̂ b) ⟦n⟧ ⟦z⟧ ⟦s⟧ = {!!} , {!!}

caseSat : ∀ {Γ} c {nzs : Fun Γ (tnat ×̂ c ×̂ (tnat ⇒ c))} →
      Bounded Γ (proj₁ ∘ nzs) ×
      T⟦ c ⟧ Γ (proj₁ ∘ proj₂ ∘ nzs) ×
      T⟦ tnat ⇒ c ⟧ Γ (proj₂ ∘ proj₂ ∘ nzs) →
      T⟦ c ⟧ Γ (c⦅ case c ⦆ ∘ nzs)
caseSat c (⟦n⟧ , ⟦z⟧ , ⟦s⟧) = caseSat' c ⟦n⟧ ⟦z⟧ ⟦s⟧


-- Constants satisfy this model

NN : STLC-KLP
NN .STLCDefinable.STLC-KLP.klp-base = NN-Base
NN .STLCDefinable.STLC-KLP.satC zero = zeroBounded
NN .STLCDefinable.STLC-KLP.satC suc τ = sucBounded
NN .STLCDefinable.STLC-KLP.satC (case a) τ = caseSat a

-- Theorem: addition is not definable with zero, suc, case.

thm : ¬ STLC-definable _ _ add
thm def = addNotBounded (def NN)

-- Q.E.D.

{-

-- The model is functions bounded by constant plus possible
-- the value of one variable.

data BoundedBy Γ (f : Fun Γ tnat) k : Set where
  bconst : (h : ∀ γ → f γ < k)
         → BoundedBy Γ f k
  bvar   : (h : ∀ γ → ∃ λ (x : Var tnat Γ) → f γ < k + V⦅ x ⦆ γ)
         → BoundedBy Γ f k

record Bounded Γ (f : Fun Γ tnat) : Set where
  constructor bounded
  field
    k  : ℕ
    bb : BoundedBy Γ f k

-- Weakening boundedness.

wkBoundedBy : ∀ {Γ Δ k} {f : C⦅ Γ ⦆ → ℕ} →
            BoundedBy Γ f k → (τ : Δ ≤ Γ) → BoundedBy Δ (f ∘ R⦅ τ ⦆) k
wkBoundedBy (bconst h) τ = bconst λ γ → h (R⦅ τ ⦆ γ)
wkBoundedBy (bvar h)   τ = bvar   λ γ →
  let (x , p) = h (R⦅ τ ⦆ γ)
  in  wkVar x τ , p  -- REWRITE wk-evalv

wkBounded : ∀ {Γ Δ} {f : C⦅ Γ ⦆ → ℕ} →
            Bounded Γ f → (τ : Δ ≤ Γ) → Bounded Δ (f ∘ R⦅ τ ⦆)
wkBounded (bounded k bb) τ = bounded k (wkBoundedBy bb τ)

-- Kripke model

NN-Base : STLC-KLP-Base
NN-Base .STLCDefinable.STLC-KLP-Base.B⟦_⟧  nat Γ f = Bounded Γ f
NN-Base .STLCDefinable.STLC-KLP-Base.monB nat τ b = wkBounded b τ

open STLC-KLP-Ext NN-Base

-- zero and suc are bounded.

zeroBounded : ∀{Γ} → Bounded Γ (λ _ → zero)
zeroBounded = bounded 1 (bconst (λ γ → s≤s z≤n))

sucBoundedBy : ∀{Γ f k} → BoundedBy Γ f k → BoundedBy Γ (suc ∘ f) (suc k)
sucBoundedBy (bconst h) = bconst λ γ → s≤s (h γ)
sucBoundedBy (bvar h)   = bvar   λ γ → let x , p = h γ in x , s≤s p

sucBounded : ∀{Γ f} → Bounded Γ f → Bounded Γ (suc ∘ f)
sucBounded (bounded k bb) = bounded (suc k) (sucBoundedBy bb)

⟦pred⟧ : ∀{Γ f} → Bounded Γ f → Bounded Γ (pred ∘ f)
⟦pred⟧ = {!!}

caseSat' : ∀ {Γ} c  {n : Fun Γ tnat} {z : Fun Γ c} {s : Fun Γ (tnat ⇒ c)} →
      (⟦n⟧ : T⟦ tnat     ⟧ Γ n) →
      (⟦z⟧ : T⟦ c        ⟧ Γ z) →
      (⟦s⟧ : T⟦ tnat ⇒ c ⟧ Γ s) →
      -- T⟦ c        ⟧ Γ (λ γ → caseN (n γ) (z γ) (s γ))
      T⟦ c        ⟧ Γ (c⦅ case c ⦆ ∘ λ γ → (n γ , z γ , s γ))
caseSat' tnat ⟦n⟧@(bounded kn hn) (bounded kz hz) ⟦s⟧ with ⟦s⟧ id≤ (⟦pred⟧ ⟦n⟧)
caseSat' tnat {n} {z} {s} (bounded kn hn) (bounded kz (bconst hz)) ⟦s⟧ | bounded ks (bconst hs) = bounded (kz + ks) (bconst (λ γ → aux γ (n γ) (hs γ)))
  where
  aux : ∀ γ m → s γ (pred m) < ks → (c⦅ case tnat ⦆ (m , z γ , s γ)) < kz + ks
  aux γ zero    _  = ≤-stepsʳ _ (hz γ)
  aux γ (suc m) hs = ≤-stepsˡ _ hs

caseSat' tnat (bounded kn hn) (bounded kz (bconst hz)) ⟦s⟧ | bounded ks (bvar hs) = bounded (kz + ks) (bvar (λ γ → {!aux γ (n γ) (hs γ)!}))
caseSat' tnat (bounded kn hn) (bounded kz (bvar hz)) ⟦s⟧ | bounded ks (bconst hs) = {!!}
caseSat' tnat (bounded kn hn) (bounded kz (bvar hz)) ⟦s⟧ | bounded ks (bvar hs) = {!!}
-- bounded (kz + ks) {!!}
caseSat' (a ⇒ b) ⟦n⟧ ⟦z⟧ ⟦s⟧ τ ⟦d⟧ = {! caseSat' b {! monT _ τ ⟦n⟧ !} {!!} {!!} !}
caseSat' (a ×̂ b) = {!!}

caseSat : ∀ {Γ} c {nzs : Fun Γ (tnat ×̂ c ×̂ (tnat ⇒ c))} →
      Bounded Γ (proj₁ ∘ nzs) ×
      T⟦ c ⟧ Γ (proj₁ ∘ proj₂ ∘ nzs) ×
      T⟦ tnat ⇒ c ⟧ Γ (proj₂ ∘ proj₂ ∘ nzs) →
      T⟦ c ⟧ Γ (c⦅ case c ⦆ ∘ nzs)
caseSat c (⟦n⟧ , ⟦z⟧ , ⟦s⟧) = caseSat' c ⟦n⟧ ⟦z⟧ ⟦s⟧


-- Constants satisfy this model


NN : STLC-KLP
NN .STLCDefinable.STLC-KLP.klp-base = NN-Base
NN .STLCDefinable.STLC-KLP.satC zero = zeroBounded
NN .STLCDefinable.STLC-KLP.satC suc τ = sucBounded
NN .STLCDefinable.STLC-KLP.satC (case a) τ = caseSat a

{-

-- Definable numbers will be finite case trees over variables
-- in the context with bodies composed from variables and constructors.

data Leaf (Γ : Cxt) : Set where
  var  : (x : Var tnat Γ) → Leaf Γ
  zero : Leaf Γ
  suc  : (b : Leaf Γ) → Leaf Γ

data Tree (Γ : Cxt) : Set where
  leaf : (b : Leaf Γ) → Tree Γ
  case : (x : Var tnat Γ) (z : Tree Γ) (s : Tree (Γ ▷ tnat)) → Tree Γ

data Nf (Γ : Cxt) : Ty → Set where
  body : (t : Tree Γ) → Nf Γ tnat
  fun  : ∀{a b} (t : Nf (Γ ▷ a) b) → Nf Γ (a ⇒ b)

-- Weakening

wkLeaf : ∀{Γ Δ} (b : Leaf Γ) (τ : Δ ≤ Γ) → Leaf Δ
wkLeaf (var x) τ = var (wkVar x τ)
wkLeaf zero    τ = zero
wkLeaf (suc b) τ = suc (wkLeaf b τ)

wkTree : ∀{Γ Δ} (t : Tree Γ) (τ : Δ ≤ Γ) → Tree Δ
wkTree (leaf b)       τ = leaf (wkLeaf b τ)
wkTree (case x t₁ t₂) τ = case (wkVar x τ) (wkTree t₁ τ) {!wkTree t₂ τ!}

wkNf : ∀{Γ Δ a} (t : Nf Γ a) (τ : Δ ≤ Γ) → Nf Δ a
wkNf (body t) τ = body (wkTree t τ)
wkNf (fun t)  τ = fun (wkNf t (lift τ))

-- Interpretation

lf⦅_⦆ : ∀{Γ} (b : Leaf Γ) → C⦅ Γ ⦆ → ℕ
lf⦅ var x ⦆ = V⦅ x ⦆
lf⦅ zero ⦆  = λ _ → zero
lf⦅ suc b ⦆ = suc ∘ lf⦅ b ⦆

tr⦅_⦆ : ∀{Γ} (t : Tree Γ) → C⦅ Γ ⦆ → ℕ
tr⦅ leaf b ⦆       = lf⦅ b ⦆
tr⦅ case x z s ⦆ γ = c⦅ case tnat ⦆ (V⦅ x ⦆ γ) (tr⦅ z ⦆ γ) λ n → tr⦅ s ⦆ (γ , n)

nf⦅_⦆ : ∀{Γ a} (t : Nf Γ a) → C⦅ Γ ⦆ → T⦅ a ⦆
nf⦅ body t ⦆ = tr⦅ t ⦆
nf⦅ fun t ⦆ γ o = nf⦅ t ⦆ (γ , o)

-- Constructions

sucTr : ∀{Γ} (t : Tree Γ) → Tree Γ
sucTr (leaf b) = leaf (suc b)
sucTr (case x t₁ t₂) = case x (sucTr t₁) (sucTr t₂)

-- Lemma: tr⦅ sucTr t ⦆ ≡ suc ∘ tr⦅ t ⦆


record IsRepresentable Γ T (f : Fun Γ T) : Set where
  constructor repr
  field
    t : Nf Γ T
    eq : nf⦅ t ⦆ ≡  f

-- record IsBounded Γ (f : Fun Γ tnat) : Set where
--   field
--     x : Var tnat Γ
--     k : ℕ

-- Above : \

-- Sum the environment entries of type nat.

sum : ∀ Γ (γ : C⦅ Γ ⦆) → ℕ
sum ε _ = 0
sum (Γ ▷ tnat)     (γ , n) = n + sum Γ γ
sum (Γ ▷ (_ ⇒ _))  (γ , _) = sum Γ γ
sum (Γ ▷ (_ ×̂ _))  (γ , _) = sum Γ γ


Bounded : ∀ {Γ} c (f : Fun ((Γ ▷ tnat) ▷ tnat) c) → Set
Bounded tnat       f = ∃ λ γ → f γ < sum _ γ
Bounded (tnat ⇒ b) f = Bounded b (uncurry f)
Bounded _          f = ⊤

varIsBounded : ∀ {Γ c} (x : Var c ((Γ ▷ tnat) ▷ tnat)) → Bounded c V⦅ x ⦆
varIsBounded vz     = {!!}
varIsBounded (vs x) = {!!}

-- A variable cannot be the addition function.

addNotVar :
  (x : Var tnat ((ε ▷ tnat) ▷ tnat))
  (h : ∀ (n m : ℕ) → V⦅ x ⦆ ((_ , n) , m) ≡ n + m) → ⊥
addNotVar vz      h = case h 1 0 of λ()
addNotVar (vs vz) h = case h 0 1 of λ()

-- A leaf cannot be the addition function.

addNotLeaf :
  (t : Leaf ((ε ▷ tnat) ▷ tnat))
  (h : ∀ (n m : ℕ) → lf⦅ t ⦆ ((_ , n) , m) ≡ n + m) → ⊥
addNotLeaf (var x) h = addNotVar x h
addNotLeaf zero    h = case h 0 1 of λ()
addNotLeaf (suc t) h = addNotLeaf t (λ n m → suc-injective {! (h (suc n) m)!})

addNotR :
  (t : Tree ((ε ▷ tnat) ▷ tnat))
  (n : ℕ)
  (h : ∀ (m : ℕ) → tr⦅ t ⦆ ((_ , n) , m) ≡ m + n) → ⊥
addNotR (leaf b) n h = {!!}
addNotR (case x t t₁) n h = {!!}

-- addNotRepresentable


-- Kripke model

NN-Base : STLC-KLP-Base
NN-Base .STLCDefinable.STLC-KLP-Base.B⟦_⟧ nat Γ f = IsRepresentable Γ _ f
NN-Base .STLCDefinable.STLC-KLP-Base.monB nat τ (repr t refl) = repr (wkNf t τ) {!!}

-- Constants satisfy this model

NN : STLC-KLP
NN .STLCDefinable.STLC-KLP.klp-base = NN-Base
NN .STLCDefinable.STLC-KLP.satC zero =
  repr (body (leaf zero)) refl
NN .STLCDefinable.STLC-KLP.satC suc τ (repr (body t) refl) =
  repr (body (sucTr t)) {!!}
NN .STLCDefinable.STLC-KLP.satC (case a) τ ⟦d⟧ τ₁ ⟦d⟧₁ τ₂ ⟦d⟧₂ = {!!}


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
