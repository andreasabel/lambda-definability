{-# OPTIONS --without-K #-} --TODO
module Model.Type where

open import Model.Exponential public
open import Model.Nat public
open import Model.Product public
open import Model.Terminal public
open import Model.Type.Core public
open import Model.Stream public
open import Model.Quantification public

open import Model.Size as MS using
  ( ≤-prop ) renaming
  ( ⟦_⟧ΔRG to ⟦_⟧Δ ; ⟦_⟧nRG to ⟦_⟧n ; ⟦_⟧σRG to ⟦_⟧σ )
open import Source.Size.Substitution.Universe as SS using (sub-syntax-Size)
open import Source.Type as ST using
  ( sub-syntax-Ctx ; sub-syntax-Type )
open import Util.Prelude hiding (id ; _∘_ ; _×_ ; ⊤)

import Source.Size as SS

open MS._≤_


⟦_⟧T : ∀ {Δ} (T : ST.Type Δ) → ⟦Type⟧ ⟦ Δ ⟧Δ
⟦ ST.Nat n ⟧T = subT ⟦ n ⟧n Nat
⟦ ST.Stream n ⟧T = subT ⟦ n ⟧n Stream
⟦ T ST.⇒ U ⟧T = ⟦ T ⟧T ↝ ⟦ U ⟧T
⟦ ST.Π n , T ⟧T = ⟦∀⟧ n ⟦ T ⟧T


⟦_⟧Γ : ∀ {Δ} (Γ : ST.Ctx Δ) → ⟦Type⟧ ⟦ Δ ⟧Δ
⟦ ST.[] ⟧Γ = ⊤
⟦ Γ ST.∙ T ⟧Γ = ⟦ Γ ⟧Γ × ⟦ T ⟧T


⇒-resp-≈⟦Type⟧ : ∀ {Γ} {T T′ U U′ : ⟦Type⟧ Γ}
  → T ≈⟦Type⟧ T′
  → U ≈⟦Type⟧ U′
  → T ⇒ U
  → T′ ⇒ U′
⇒-resp-≈⟦Type⟧ T≈T′ U≈U′ f = U≈U′ .forth ∘ f ∘ T≈T′ .back


⟦subT⟧ : ∀ {Δ Ω} (σ : SS.Sub Δ Ω) (T : ST.Type Ω)
  → ⟦ T [ σ ]T ⟧T ≈⟦Type⟧ subT ⟦ σ ⟧σ ⟦ T ⟧T
⟦subT⟧ {Δ} {Ω} σ (ST.Nat n) = record
  { forth = record
    { fobj = castℕ≤ (reflexive (MS.⟦sub⟧ σ n))
    ; feq = λ γ≈γ′ m≡m → m≡m
    }
  ; back = record
    { fobj = castℕ≤ (reflexive (sym (MS.⟦sub⟧ σ n)))
    ; feq = λ γ≈γ′ m≡m → m≡m
    }
  ; back-forth = ≈⁺ λ γ x → ℕ≤-≡⁺ _ _ refl
  ; forth-back = ≈⁺ λ γ x → ℕ≤-≡⁺ _ _ refl
  }
⟦subT⟧ {Δ} {Ω} σ (ST.Stream n) = record
  { forth = record
    { fobj = castColist (reflexive (sym (MS.⟦sub⟧ σ n)))
    ; feq = λ γ≈γ′ xs≈ys a a₁ a₂ → xs≈ys _ _ _
    }
  ; back = record
    { fobj = castColist (reflexive (MS.⟦sub⟧ σ n))
    ; feq = λ γ≈γ′ xs≈ys a a₁ a₂ → xs≈ys _ _ _
    }
  ; back-forth = ≈⁺ λ γ xs → Colist-≡⁺ λ m m≤n → cong (xs m) (≤-prop _ _)
  ; forth-back = ≈⁺ λ γ xs → Colist-≡⁺ λ m m≤n → cong (xs m) (≤-prop _ _)
  }
⟦subT⟧ {Δ} {Ω} σ (T ST.⇒ U)
  -- Giving the implicit arguments explicitly here is very good for performance.
  = ≈⟦Type⟧-trans {⟦ Δ ⟧Δ} {⟦ (T ST.⇒ U) [ σ ]T ⟧T}
      {subT ⟦ σ ⟧σ ⟦ T ⟧T ↝ subT ⟦ σ ⟧σ ⟦ U ⟧T}
      {subT ⟦ σ ⟧σ ⟦ T ST.⇒ U ⟧T}
      (↝-resp-≈⟦Type⟧ {⟦ Δ ⟧Δ} {⟦ T [ σ ]T ⟧T} {subT ⟦ σ ⟧σ ⟦ T ⟧T}
        {⟦ U [ σ ]T ⟧T} {subT ⟦ σ ⟧σ ⟦ U ⟧T} (⟦subT⟧ σ T) (⟦subT⟧ σ U))
      (subT-↝ {⟦ Δ ⟧Δ} {⟦ Ω ⟧Δ} ⟦ σ ⟧σ ⟦ T ⟧T ⟦ U ⟧T)
⟦subT⟧ {Δ} {Ω} σ (ST.Π n , T)
  -- Ditto here, especially the 'n's.
  = ≈⟦Type⟧-trans {⟦ Δ ⟧Δ} {⟦∀⟧ (n [ σ ]n) ⟦ T [ SS.Keep′ σ ]T ⟧T}
      {⟦∀⟧ (n [ σ ]n) (subT ⟦ SS.Keep′ {n = n} σ ⟧σ ⟦ T ⟧T)}
      {subT ⟦ σ ⟧σ (⟦∀⟧ n ⟦ T ⟧T)}
      (⟦∀⟧-resp-≈⟦Type⟧ {Δ} (n [ σ ]n) {⟦ T [ SS.Keep′ {n = n} σ ]T ⟧T}
        {subT ⟦ SS.Keep′ {n = n} σ ⟧σ ⟦ T ⟧T}
        (⟦subT⟧ {Δ SS.∙ n [ σ ]n} {Ω SS.∙ n} (SS.Keep′ {n = n} σ) T))
      (subT-⟦∀⟧ {Δ} {Ω} {n} σ ⟦ T ⟧T)


⟦subΓ⟧ : ∀ {Δ Ω} (σ : SS.Sub Δ Ω) (Γ : ST.Ctx Ω)
  → ⟦ Γ [ σ ]Γ ⟧Γ ≈⟦Type⟧ subT ⟦ σ ⟧σ ⟦ Γ ⟧Γ
⟦subΓ⟧ σ ST.[] = record
  { forth = record { fobj = λ x → x ; feq = λ γ≈γ′ x → x }
  ; back = record { fobj = λ x → x ; feq = λ γ≈γ′ x → x }
  ; back-forth = ≈⁺ λ γ x → refl
  ; forth-back = ≈⁺ λ γ x → refl
  }
⟦subΓ⟧ σ (Γ ST.∙ T) = ×-resp-≈⟦Type⟧ (⟦subΓ⟧ σ Γ) (⟦subT⟧ σ T)


subₛ
  : ∀ {Δ Ω} Γ T
  → (σ : SS.Sub Δ Ω)
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T
  → ⟦ Γ [ σ ]Γ ⟧Γ ⇒ ⟦ T [ σ ]T ⟧T
subₛ Γ T σ f
  = ⟦subT⟧ σ T .back ∘ subt ⟦ σ ⟧σ f ∘ ⟦subΓ⟧ σ Γ .forth


≡→≈⟦Type⟧Γ : ∀ {Δ} {Γ Ψ : ST.Ctx Δ}
  → Γ ≡ Ψ
  → ⟦ Γ ⟧Γ ≈⟦Type⟧ ⟦ Ψ ⟧Γ
≡→≈⟦Type⟧Γ p = ≡→≈⟦Type⟧ (cong ⟦_⟧Γ p)


≡→≈⟦Type⟧T : ∀ {Δ} {T U : ST.Type Δ}
  → T ≡ U
  → ⟦ T ⟧T ≈⟦Type⟧ ⟦ U ⟧T
≡→≈⟦Type⟧T p = ≡→≈⟦Type⟧ (cong ⟦_⟧T p)
