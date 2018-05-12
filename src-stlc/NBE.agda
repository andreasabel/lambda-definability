
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; curry)

open import Function using (id; _∘_; _∘′_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

-- {-# BUILTIN REWRITE _≡_ #-}

import SimpleTypes

module NBE
  (Base : Set)  (B⦅_⦆ : Base → Set) (open SimpleTypes Base B⦅_⦆)
  (Const : Set) (ty : Const → Ty) (c⦅_⦆ : (c : Const) → T⦅ ty c ⦆)
  where

open import STLCDefinable Base B⦅_⦆ Const ty c⦅_⦆

-- Normal forms

mutual
  data Neutral : ∀ {Γ T} (t : Tm Γ T) → Set where
    neCon : ∀ {Γ} (c : Const) → Neutral {Γ} (con c)
    neVar : ∀ {Γ T} (x : Var T Γ) → Neutral (var x)
    neApp : ∀ {Γ T U} {t : Tm Γ (U ⇒ T)} {u : Tm Γ U}
      (ne : Neutral t) (nf : Normal u) → Neutral (app t u)

  data Normal {Γ} : ∀ {T} (t : Tm Γ T) → Set where
    nfNe  : ∀{T} {t : Tm Γ T} (ne : Neutral t) → Normal t
    nfAbs : ∀{T U} {t : Tm (Γ ▷ U) T} (nf : Normal t) → Normal (abs t)

-- Weakening normal forms

mutual
  wkNe : ∀{Γ Δ T} {t : Tm Γ T} (ne : Neutral t) (τ : Δ ≤ Γ) → Neutral (t w[ τ ]ᵉ)
  wkNe (neCon c)     τ = neCon c
  wkNe (neVar x)     τ = neVar _
  wkNe (neApp ne nf) τ = neApp (wkNe ne τ) (wkNf nf τ)

  wkNf : ∀{Γ Δ T} {t : Tm Γ T} (nf : Normal t) (τ : Δ ≤ Γ) → Normal (t w[ τ ]ᵉ)
  wkNf (nfNe  ne) τ = nfNe (wkNe ne τ)
  wkNf (nfAbs nf) τ = nfAbs (wkNf nf _)

-- A syntactical klp: being the image of a normal form

NeImg : ∀ Γ T (f : Fun Γ T) → Set
NeImg Γ T f = ∃ λ (t : Tm Γ T) → Neutral t × E⦅ t ⦆ ≡ f

NfImg : ∀ Γ T (f : Fun Γ T) → Set
NfImg Γ T f = ∃ λ (t : Tm Γ T) → Normal t × E⦅ t ⦆ ≡ f

neImgToNf : ∀{Γ T f} → NeImg Γ T f → NfImg Γ T f
neImgToNf (t , ne , p) = (t , nfNe ne , p)

NfKLP-Base : STLC-KLP-Base
NfKLP-Base .STLC-KLP-Base.B⟦_⟧ b Γ f                =  NeImg Γ (base b) f
NfKLP-Base .STLC-KLP-Base.monB b τ (t , ne , refl)  =  t w[ τ ]ᵉ , wkNe ne τ , wk-eval t τ

-- Reflection / reification

module _ (open STLC-KLP-Ext NfKLP-Base) where
  mutual

    reflectNe : ∀{Γ} T (t : Tm Γ T) (ne : Neutral t) → T⟦ T ⟧ Γ E⦅ t ⦆
    reflectNe (base b) t ne = t , ne , refl
    reflectNe {Γ} (U ⇒ T) t ne {Δ} τ {d} ⟦d⟧ with reifyNf U ⟦d⟧
    reflectNe {Γ} (U ⇒ T) t ne {Δ} τ {d} ⟦d⟧ | u , nf , refl = reflectNe T (app (t w[ τ ]ᵉ) u) (neApp (wkNe ne τ) nf) -- REWRITE wk-eval

    reifyNf : ∀{Γ} T {f : Fun Γ T} (⟦f⟧ : T⟦ T ⟧ Γ f) → NfImg Γ T f
    reifyNf (base b) ⟦f⟧ = neImgToNf ⟦f⟧
    reifyNf (U ⇒ T) ⟦f⟧ with reifyNf T (⟦f⟧ (weak id≤) {proj₂} (reflectNe U (var vz) (neVar _)))
    ... | t , nf , ⦅t⦆≡uncurryf = abs t , nfAbs nf , cong curry ⦅t⦆≡uncurryf

NfKLP : STLC-KLP
NfKLP .STLC-KLP.klp-base = NfKLP-Base
NfKLP .STLC-KLP.satC c = reflectNe (ty c) (con c) (neCon c)


-- open Fund Nf

{-
-- Identity environment

idEnv : ∀ Γ → C⟦ Γ ⟧ Γ id
idEnv Γ = ?

nbe : ∀{Γ T} (t : Tm Γ T) → NfImg Γ T E⦅ t ⦆
nbe t = ?
-}
