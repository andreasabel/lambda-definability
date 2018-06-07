-- A term model yielding normalization

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Library
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

record NeImg Γ T (f : Fun Γ T) : Set where
  constructor neImg; field
    {t} : Tm Γ T
    ne  : Neutral t
    eq  : E⦅ t ⦆ ≡ f

record NfImg Γ T (f : Fun Γ T) : Set where
  constructor nfImg; field
    {t} : Tm Γ T
    nf  : Normal t
    eq  : E⦅ t ⦆ ≡ f

neImgToNf : ∀{Γ T f} → NeImg Γ T f → NfImg Γ T f
neImgToNf (neImg ne eq) = nfImg (nfNe ne) eq

nfImgAbs : ∀{Γ T U f} → NfImg (Γ ▷ U) T f → NfImg Γ (U ⇒ T) (curry f)
nfImgAbs (nfImg nf ⦅nf⦆≡f) = nfImg (nfAbs nf) (cong curry ⦅nf⦆≡f)

NfKLP-Base : STLC-KLP-Base
NfKLP-Base .STLC-KLP-Base.B⟦_⟧ b Γ f                    =  NeImg Γ (base b) f
NfKLP-Base .STLC-KLP-Base.monB b τ (neImg {t} ne refl)  =  neImg (wkNe ne τ) (wk-eval t τ)

-- Reflection / reification

module _ (open STLC-KLP-Ext NfKLP-Base) where
  mutual

    reflectNe : ∀{Γ} T {t : Tm Γ T} (ne : Neutral t) → T⟦ T ⟧ Γ E⦅ t ⦆
    reflectNe (base b) ne = neImg ne refl
    reflectNe (U ⇒ T) ne τ ⟦d⟧ with reifyNf U ⟦d⟧
    ... | nfImg nf refl = reflectNe T (neApp (wkNe ne τ) nf) -- REWRITE wk-eval

    reifyNf : ∀{Γ} T {f : Fun Γ T} (⟦f⟧ : T⟦ T ⟧ Γ f) → NfImg Γ T f
    reifyNf (base b) ⟦f⟧ = neImgToNf ⟦f⟧
    reifyNf (U ⇒ T) ⟦f⟧ = nfImgAbs (reifyNf T (⟦f⟧ (weak id≤) (reflectNe U (neVar vz))))

NfKLP : STLC-KLP
NfKLP .STLC-KLP.klp-base = NfKLP-Base
NfKLP .STLC-KLP.satC c = reflectNe (ty c) (neCon c)

open Fund NfKLP

-- Identity environment

idEnv : ∀ Γ → C⟦ Γ ⟧ Γ id
idEnv ε = _
idEnv (Γ ▷ U) = monC Γ (weak id≤) (idEnv Γ) , reflectNe U (neVar vz)

nbe : ∀{Γ T} (t : Tm Γ T) → NfImg Γ T E⦅ t ⦆
nbe t = reifyNf _ (fund t (idEnv _))

-- -}

-- -}
