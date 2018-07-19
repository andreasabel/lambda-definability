-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, May/June 2018

-- 3. Adapting reflection/reification to obtain normalization

-- The proof of reflection and reification does not introduce β-redexes,
-- thus, we can strengthen it to work on β-normal forms.

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

open import Library
import SimpleTypes

module NBE
  (Base : Set)  (B⦅_⦆ : Base → Set) (open SimpleTypes Base B⦅_⦆)
  (Const : Set) (ty : Const → Ty) (c⦅_⦆ : (c : Const) → T⦅ ty c ⦆)
  where

open import STLCDefinable Base B⦅_⦆ Const ty c⦅_⦆

-- β-normal forms obtained as a restriction of terms.
-- Uses the auxiliary concept of "neutral" which characterizes
-- normal eliminations from a variable or constant.

mutual

  -- Neutral are constants and variables and their application to normal forms.

  data Neutral : ∀ {Γ T} (t : Tm Γ T) → Set where
    neCon : ∀ {Γ} (c : Const) → Neutral {Γ} (con c)
    neVar : ∀ {Γ T} (x : Var T Γ) → Neutral (var x)
    neApp : ∀ {Γ T U} {t : Tm Γ (U ⇒ T)} {u : Tm Γ U}
      (ne : Neutral t) (nf : Normal u) → Neutral (app t u)
    neFst : ∀ {Γ T U} {t : Tm Γ (U ×̂ T)} (ne : Neutral t) → Neutral (fst t)
    neSnd : ∀ {Γ T U} {t : Tm Γ (U ×̂ T)} (ne : Neutral t) → Neutral (snd t)
    neREC : ∀ {Γ T} {z : Tm Γ T} {s : Tm Γ (N ⇒ (T ⇒ T))} {n : Tm Γ N} → Normal z → Normal s → Neutral n → Neutral (recN z s n)

  -- A normal form is a neutral unter a prefix of λ-abstractions.

  data Normal {Γ} : ∀ {T} (t : Tm Γ T) → Set where
    nfNe   : ∀{T} {t : Tm Γ T} (ne : Neutral t) → Normal t
    nfAbs  : ∀{T U} {t : Tm (Γ ▷ U) T} (nf : Normal t) → Normal (abs t)
    nfPair : ∀{T U} {t : Tm Γ U} {u : Tm Γ T} (nf₁ : Normal t) (nf₂ : Normal u) → Normal (pair t u)
    nfZ : Normal zero
    nfS : ∀ {n : Tm Γ N} → Normal n → Normal (suc n)

-- Weakening normal forms

mutual
  wkNe : ∀{Γ Δ T} {t : Tm Γ T} (ne : Neutral t) (τ : Δ ≤ Γ) → Neutral (t w[ τ ]ᵉ)
  wkNe (neCon c)     τ = neCon c
  wkNe (neVar x)     τ = neVar _
  wkNe (neApp ne nf) τ = neApp (wkNe ne τ) (wkNf nf τ)
  wkNe (neFst ne)    τ = neFst (wkNe ne τ)
  wkNe (neSnd ne)    τ = neSnd (wkNe ne τ)
  wkNe (neREC z s n) τ = neREC (wkNf z τ) (wkNf s τ) (wkNe n τ)

  wkNf : ∀{Γ Δ T} {t : Tm Γ T} (nf : Normal t) (τ : Δ ≤ Γ) → Normal (t w[ τ ]ᵉ)
  wkNf (nfNe  ne) τ = nfNe (wkNe ne τ)
  wkNf (nfAbs nf) τ = nfAbs (wkNf nf _)
  wkNf (nfPair nf₁ nf₂) τ = nfPair (wkNf nf₁ τ) (wkNf nf₂ τ)
  wkNf nfZ τ = nfZ
  wkNf (nfS nf) τ = nfS (wkNf nf τ)

-- A syntactical KLP: being the image of a normal form.

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

-- Derived constructors of NfImg.

neImgToNf : ∀{Γ T f} → NeImg Γ T f → NfImg Γ T f
neImgToNf (neImg ne eq) = nfImg (nfNe ne) eq

nfImgAbs : ∀{Γ T U f} → NfImg (Γ ▷ U) T f → NfImg Γ (U ⇒ T) (curry f)
nfImgAbs (nfImg nf ⦅nf⦆≡f) = nfImg (nfAbs nf) (cong curry ⦅nf⦆≡f)

nfImgPair : ∀ {Γ U T f} → NfImg Γ U (proj₁ ∘ f) → NfImg Γ T (proj₂ ∘ f) → NfImg Γ (U ×̂ T) f
nfImgPair (nfImg t ⦅t⦆≡f) (nfImg u ⦅u⦆≡g) = nfImg (nfPair t u) (cong₂ <_,_> ⦅t⦆≡f ⦅u⦆≡g)

-- A Kripke model of images of normal forms.
-- At base type, a normal form is necessarily neutral.

NfKLP-Base : STLC-KLP-Base
NfKLP-Base .STLC-KLP-Base.B⟦_⟧ b Γ f                    =  NeImg Γ (base b) f
NfKLP-Base .STLC-KLP-Base.monB b τ (neImg {t} ne refl)  =  neImg (wkNe ne τ) (wk-eval t τ)
NfKLP-Base .STLC-KLP-Base.⟦N⟧ Γ f = NfImg Γ N f
NfKLP-Base .STLC-KLP-Base.monN τ (nfImg {t} nf refl) = nfImg (wkNf nf τ) (wk-eval t τ)

-- Reflection / reification

-- This time, the proof also maintains witnesses of neutrality / normality.

module _ (open STLC-KLP-Ext NfKLP-Base) where
  mutual

    reflectNe : ∀{Γ} T {t : Tm Γ T} (ne : Neutral t) → T⟦ T ⟧ Γ E⦅ t ⦆
    reflectNe (base b) ne = neImg ne refl
    reflectNe (U ⇒ T) ne τ ⟦d⟧ with reifyNf U ⟦d⟧
    ... | nfImg nf refl = reflectNe T (neApp (wkNe ne τ) nf) -- REWRITE wk-eval
    reflectNe (U ×̂ T) ne = reflectNe U (neFst ne) , reflectNe T (neSnd ne)
    reflectNe N ne = nfImg (nfNe ne) refl

    reifyNf : ∀{Γ} T {f : Fun Γ T} (⟦f⟧ : T⟦ T ⟧ Γ f) → NfImg Γ T f
    reifyNf (base b) ⟦f⟧ = neImgToNf ⟦f⟧
    reifyNf (U ⇒ T) ⟦f⟧ = nfImgAbs (reifyNf T (⟦f⟧ (weak id≤) (reflectNe U (neVar vz))))
    reifyNf (U ×̂ T) (⟦f⟧ , ⟦g⟧) = nfImgPair (reifyNf U ⟦f⟧) (reifyNf T ⟦g⟧)
    reifyNf N ⟦f⟧ = ⟦f⟧

NfKLP : STLC-KLP
NfKLP .STLC-KLP.klp-base = NfKLP-Base
NfKLP .STLC-KLP.satC c = reflectNe (ty c) (neCon c)
NfKLP .STLC-KLP.satZ = nfImg nfZ refl
NfKLP .STLC-KLP.satS (nfImg nf refl) = nfImg (nfS nf) refl
NfKLP .STLC-KLP.satREC z s (nfImg nfZ refl) = z
NfKLP .STLC-KLP.satREC {T} z s (nfImg (nfS {n'} nf) refl) =
  s id≤ (nfImg nf refl) id≤ (NfKLP .STLC-KLP.satREC {T} z s (nfImg nf refl))
NfKLP .STLC-KLP.satREC {T} {⦅s⦆ = ⦅s⦆} z s (nfImg (nfNe ne) refl)
    with reifyNf T z | reifyNf (N ⇒ (T ⇒ T)) {⦅s⦆} s
... | nfImg nf refl | nfImg nf₁ refl = reflectNe T (neREC nf nf₁ ne)


open Fund NfKLP

-- Identity environment

idEnv : ∀ Γ → C⟦ Γ ⟧ Γ id
idEnv ε = _
idEnv (Γ ▷ U) = monC Γ (weak id≤) (idEnv Γ) , reflectNe U (neVar vz)

-- Normalization by evaluation

-- For every well-typed term, we obtain a normal form with the same denotation.

nbe : ∀{Γ T} (t : Tm Γ T) → NfImg Γ T E⦅ t ⦆
nbe t = reifyNf _ (fund t (idEnv _))
