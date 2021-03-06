-- The purpose of this universe construction is to get some definitional
-- equalities in the model. Specifically, if we define ⟦σ⟧ : ⟦Δ⟧ → ⟦Ω⟧
-- (a functor) for the "canonical" notion of subsitution, then we have
-- ⟦Wk⟧ (δ , m) ≡ δ propositionally, but *not* definitionally. This then
-- complicates proofs involving ⟦Wk⟧, and similar for the other substitutions.

{-# OPTIONS --without-K --safe #-}
module Source.Size.Substitution.Universe where

open import Relation.Binary using (IsEquivalence ; Setoid)

open import Source.Size
open import Source.Size.Substitution.Canonical as Can using (Sub⊢)
open import Util.Prelude

import Relation.Binary.Reasoning.Setoid as SetoidReasoning


infix  4 _≈_
infixl 5 _>>_


data Sub : (Δ Ω : Ctx) → Set where
  Id : Sub Δ Δ
  _>>_ : (σ : Sub Δ Δ′) (τ : Sub Δ′ Ω) → Sub Δ Ω
  Wk : Sub (Δ ∙ n) Δ
  Lift : (σ : Sub Δ Ω) → Sub (Δ ∙ m) (Ω ∙ n)
  Fill : (n : Size Δ) → Sub Δ (Δ ∙ m)
  Skip : Sub (Δ ∙ n ∙ v0) (Δ ∙ n)


⟨_⟩ : Sub Δ Ω → Can.Sub Δ Ω
⟨ Id ⟩ = Can.Id
⟨ σ >> τ ⟩ = ⟨ σ ⟩ Can.>> ⟨ τ ⟩
⟨ Wk ⟩ = Can.Wk
⟨ Lift σ ⟩ = Can.Lift ⟨ σ ⟩
⟨ Fill n ⟩ = Can.Fill n
⟨ Skip ⟩ = Can.Skip


subV : (σ : Sub Δ Ω) (x : Var Ω) → Size Δ
subV σ = Can.subV ⟨ σ ⟩


sub : (σ : Sub Δ Ω) (n : Size Ω) → Size Δ
sub σ = Can.sub ⟨ σ ⟩


pattern Lift′ σ ⊢n = Lift σ ⊢n refl


variable σ τ ι : Sub Δ Ω


data Sub⊢ᵤ : ∀ Δ Ω → Sub Δ Ω → Set where
  Id : Sub⊢ᵤ Δ Δ Id
  comp : (⊢σ : Sub⊢ᵤ Δ Δ′ σ) (⊢τ : Sub⊢ᵤ Δ′ Δ″ τ) → Sub⊢ᵤ Δ Δ″ (σ >> τ)
  Wk : Sub⊢ᵤ (Δ ∙ n) Δ Wk
  Lift : (⊢σ : Sub⊢ᵤ Δ Ω σ) (m≡n[σ] : m ≡ sub σ n)
    → Sub⊢ᵤ (Δ ∙ m) (Ω ∙ n) (Lift σ)
  Fill : (n<m : n < m) → Sub⊢ᵤ Δ (Δ ∙ m) (Fill n)
  Skip : Sub⊢ᵤ (Δ ∙ n ∙ v0) (Δ ∙ n) Skip


syntax Sub⊢ᵤ Δ Ω σ = σ ∶ Δ ⇒ᵤ Ω


⟨⟩-resp-⊢ : σ ∶ Δ ⇒ᵤ Ω → ⟨ σ ⟩ ∶ Δ ⇒ Ω
⟨⟩-resp-⊢ Id = Can.Id⊢
⟨⟩-resp-⊢ (comp ⊢σ ⊢τ) = Can.>>⊢ (⟨⟩-resp-⊢ ⊢σ) (⟨⟩-resp-⊢ ⊢τ)
⟨⟩-resp-⊢ Wk = Can.Wk⊢
⟨⟩-resp-⊢ (Lift ⊢σ m≡n[σ]) = Can.Lift⊢ (⟨⟩-resp-⊢ ⊢σ) m≡n[σ]
⟨⟩-resp-⊢ (Fill n<m) = Can.Fill⊢ n<m
⟨⟩-resp-⊢ Skip = Can.Skip⊢


record _≈_ (σ τ : Sub Δ Ω) : Set where
  constructor ≈⁺
  field ≈⁻ : ⟨ σ ⟩ ≡ ⟨ τ ⟩

open _≈_ public


≈-refl : σ ≈ σ
≈-refl = ≈⁺ refl


≈-sym : σ ≈ τ → τ ≈ σ
≈-sym (≈⁺ p) = ≈⁺ (sym p)


≈-trans : σ ≈ τ → τ ≈ ι → σ ≈ ι
≈-trans (≈⁺ p) (≈⁺ q) = ≈⁺ (trans p q)


≈-isEquivalence : IsEquivalence (_≈_ {Δ} {Ω})
≈-isEquivalence = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }


Sub-setoid : (Δ Ω : Ctx) → Setoid 0ℓ 0ℓ
Sub-setoid Δ Ω = record
  { Carrier = Sub Δ Ω
  ; _≈_ = _≈_
  ; isEquivalence = ≈-isEquivalence
  }


module ≈-Reasoning {Δ} {Ω} = SetoidReasoning (Sub-setoid Δ Ω)


abstract
  >>-resp-≈ : {σ σ′ : Sub Δ Δ′} {τ τ′ : Sub Δ′ Δ″}
    → σ ≈ σ′ → τ ≈ τ′ → σ >> τ ≈ σ′ >> τ′
  >>-resp-≈ (≈⁺ p) (≈⁺ q) = ≈⁺ (cong₂ Can._>>_ p q)


  Lift-resp-≈ : σ ≈ τ → Lift {m = m} {n} σ ≈ Lift τ
  Lift-resp-≈ (≈⁺ p) = ≈⁺ (cong Can.Lift p)


  sub-resp-< : σ ∶ Δ ⇒ᵤ Ω → n < m → sub σ n < sub σ m
  sub-resp-< ⊢σ = Can.sub-resp-< (⟨⟩-resp-⊢ ⊢σ)


mutual
  subV′ : Sub Δ Ω → Var Ω → Size Δ
  subV′ Id x = var x
  subV′ (σ >> τ) x = sub′ σ (subV′ τ x)
  subV′ Wk x = var (suc x)
  subV′ (Lift σ) zero = var zero
  subV′ (Lift σ) (suc x) = wk (subV′ σ x)
  subV′ (Fill n) zero = n
  subV′ (Fill n) (suc x) = var x
  subV′ Skip zero = var zero
  subV′ Skip (suc x) = var (suc (suc x))


  sub′ : Sub Δ Ω → Size Ω → Size Δ
  sub′ σ (var x) = subV′ σ x
  sub′ σ ∞ = ∞
  sub′ σ ⋆ = ⋆
  sub′ σ zero = zero
  sub′ σ (suc n) = suc (sub′ σ n)


  abstract
    subV′≡subV : ∀ (σ : Sub Δ Ω) x → subV′ σ x ≡ subV σ x
    subV′≡subV Id x = sym (Can.subV-Id x)
    subV′≡subV (σ >> τ) x
      = trans (sub′≡sub σ (subV′ τ x))
          (trans (cong (sub σ) (subV′≡subV τ x))
            (sym (Can.subV->> ⟨ σ ⟩ ⟨ τ ⟩ x)))
    subV′≡subV Wk x = sym (Can.sub-Wk (var x))
    subV′≡subV (Lift σ) zero = refl
    subV′≡subV (Lift σ) (suc x)
      = trans (cong wk (subV′≡subV σ x)) (sym (Can.subV-Weaken ⟨ σ ⟩ x))
    subV′≡subV (Fill n) zero = refl
    subV′≡subV (Fill n) (suc x) = sym (Can.subV-Id x)
    subV′≡subV Skip zero = refl
    subV′≡subV Skip (suc x) = sym
      (trans (Can.subV-Weaken (Can.Weaken Can.Id) x) (cong wk (Can.sub-Wk (var x))))


    sub′≡sub : ∀ (σ : Sub Δ Ω) n → sub′ σ n ≡ sub σ n
    sub′≡sub σ (var x) = subV′≡subV σ x
    sub′≡sub σ ∞ = refl
    sub′≡sub σ ⋆ = refl
    sub′≡sub σ zero = refl
    sub′≡sub σ (suc n) = cong suc (sub′≡sub σ n)
