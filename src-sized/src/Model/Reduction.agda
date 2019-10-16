{-# OPTIONS --without-K #-}
module Model.Reduction where

open import Cats.Category

open import Model.Size using () renaming (⟦_⟧σRG to ⟦_⟧σ)
open import Model.Term
open import Model.Type as MT
open import Source.Reduction
open import Source.Size.Substitution.Universe as SU using (sub-syntax-Size)
open import Source.Term
open import Source.Type as ST using (sub-syntax-Ctx ; sub-syntax-Type)
open import Util.Prelude as Prelude renaming (_∘_ to _∘F_)
open import Util.Relation.Binary.PropositionalEquality using (happly ; ×-≡⁺)

import Model.RGraph as RG
import Source.Size as SS
import Source.Size.Substitution.Canonical as SC

open Category._≅_

open SS.Ctx


⟦subΓ⟧∘≡→≈⟦Type⟧ : ∀ {Δ Ω} {σ : SU.Sub Δ Ω} {Γ : ST.Ctx Δ} {Ψ : ST.Ctx Ω}
  → (p : Γ ≡ Ψ [ σ ]Γ)
  → ⟦subΓ⟧ σ Ψ .forth ∘ ≡→≈⟦Type⟧ (cong ⟦_⟧Γ p) .forth ≈ {!!}
⟦subΓ⟧∘≡→≈⟦Type⟧ = {!!}


CanonT : ∀ {Δ Ω} (σ : SU.Sub Δ Ω) (T : ST.Type Ω)
  → ⟦ T [ σ ]T ⟧T ⇒ subT ⟦ σ ⟧σ ⟦ T ⟧T → Set
CanonT σ (ST.Nat n) f
  = ∀ {δ} i → f .fobj {δ} i .proj₁ ≡ i .proj₁
CanonT σ (ST.Stream n) f
  = ∀ {δ} is m m≤n₀ m≤n₁ → f .fobj {δ} is m m≤n₀ ≡ is m m≤n₁
CanonT σ (T ST.⇒ U) f = {!!}
CanonT σ (ST.Π n , T) f = {!!}


CanonΓ : ∀ {Δ Ω} (σ : SU.Sub Δ Ω) (Γ : ST.Ctx Ω)
  → ⟦ Γ [ σ ]Γ ⟧Γ ⇒ subT ⟦ σ ⟧σ ⟦ Γ ⟧Γ → Set
CanonΓ σ ST.[] f = Prelude.⊤
CanonΓ σ (Γ ST.∙ T) f = {!!}


lem₀ : ∀ {Δ Ω} (σ : SU.Sub Δ Ω) T U
  → (p : T ≡ U [ σ ]T)
  → ⟦subT⟧ σ U .forth ∘ ≡→≈⟦Type⟧ (cong ⟦_⟧T p) .forth
  ≈ {!!}
lem₀ = {!!}


lem : ∀ {Δ} (T : ST.Type Δ) {n} (m m<n)
  → (p : T ≡ T [ SU.Wk ]T [ SU.Fill m m<n ]T)
  → ⟦subT⟧ (SU.Fill m m<n) (T [ SU.Wk {n = n} ]T) .forth ∘
    ≡→≈⟦Type⟧ (cong ⟦_⟧T p) .forth
  ≈ subt ⟦ SU.Fill m m<n ⟧σ (⟦subT⟧ SU.Wk T .back)
lem (ST.Nat k) {n} m m<n p = ≈⁺ λ δ γ → ℕ≤-≡⁺ _ _ {!p!}
lem (ST.Stream k) {n} m m<n p = ≈⁺ λ δ γ → Colist-≡⁺ λ o o≤k → {!!}
lem (T ST.⇒ U) {n} m m<n p = {!!}
lem (ST.Π k , T) {n} m m<n p = {!!}


interp : ∀ {Δ Γ t u T}
  → (p : Δ , Γ ⊢ t ⟶ u ∶ T)
  → ⟦ ⟶→⊢ₗ p ⟧t ≈ ⟦ ⟶→⊢ᵣ p ⟧t
interp (app-abs t u ⊢t ⊢u) = {!!}
interp {Δ} {Γ} (appₛ-absₛ n {T = T} t m ⊢t m<n) =
  let open ≈-Reasoning in ≈-sym (
  begin
    ⟦ ⟶→⊢ᵣ (appₛ-absₛ n t m ⊢t m<n) ⟧t
  ≡⟨⟩
    ⟦ cast⊢Γ (⟶→⊢ᵣ.eq n m t m<n ⊢t) (subₛ-resp-⊢ (SU.Fill m m<n) ⊢t) ⟧t
  ≈⟨ ⟦cast⊢Γ⟧ _ (subₛ-resp-⊢ (SU.Fill m m<n) ⊢t) ⟩
    ⟦ subₛ-resp-⊢ (SU.Fill m m<n) ⊢t ⟧t ∘
    ≡→≈⟦Type⟧ (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq n m t m<n ⊢t)) .back
  ≈⟨ ⟦Types⟧.∘-resp-l {g = ≡→≈⟦Type⟧ (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq n m t m<n ⊢t)) .back}
      (⟦subₛ⟧ (SU.Fill m m<n) ⊢t) ⟩
    MT.subₛ (Γ [ SU.Wk ]Γ) T (SU.Fill m m<n) ⟦ ⊢t ⟧t ∘
    ≡→≈⟦Type⟧ (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq n m t m<n ⊢t)) .back
  ≡⟨⟩
    (⟦subT⟧ (SU.Fill m m<n) T .back ∘
     subt ⟦ SU.Fill m m<n ⟧σ ⟦ ⊢t ⟧t ∘
     ⟦subΓ⟧ (SU.Fill m m<n) (Γ [ SU.Wk ]Γ) .forth) ∘
    ≡→≈⟦Type⟧ (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq n m t m<n ⊢t)) .back
  ≈⟨ {!!} ⟩ -- trivial
    ⟦subT⟧ (SU.Fill m m<n) T .back ∘
    subt ⟦ SU.Fill m m<n ⟧σ ⟦ ⊢t ⟧t ∘
    (⟦subΓ⟧ (SU.Fill m m<n) (Γ [ SU.Wk ]Γ) .forth ∘
    ≡→≈⟦Type⟧ (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq n m t m<n ⊢t)) .back)
  ≈⟨ {!⟦subΓ⟧ (SU.Fill m m<n) (Γ [ SU.Wk ]Γ) .forth!} ⟩
    ⟦subT⟧ (SU.Fill m m<n) T .back ∘
    subt ⟦ SU.Fill m m<n ⟧σ ⟦ ⊢t ⟧t ∘
    subt ⟦ SU.Fill m m<n ⟧σ (⟦subΓ⟧ SU.Wk Γ .back)
  ≈˘⟨ ⟦Types⟧.∘-resp-r {f = ⟦subT⟧ (SU.Fill m m<n) T .back}
      (subt-∘ ⟦ SU.Fill m m<n ⟧σ ⟦ ⊢t ⟧t (⟦subΓ⟧ SU.Wk Γ .back)) ⟩
    ⟦subT⟧ (SU.Fill m m<n) T .back ∘
    subt ⟦ SU.Fill m m<n ⟧σ (⟦ ⊢t ⟧t ∘ ⟦subΓ⟧ SU.Wk Γ .back)
  ≈˘⟨ ⟦Types⟧.∘-resp-r {f = ⟦subT⟧ (SU.Fill m m<n) T .back}
      (appₛ∘absₛ m m<n (⟦ ⊢t ⟧t ∘ ⟦subΓ⟧ SU.Wk Γ .back)) ⟩
    ⟦subT⟧ (SU.Fill m m<n) T .back ∘
    MT.appₛ m m<n (MT.absₛ (⟦ ⊢t ⟧t ∘ ⟦subΓ⟧ SU.Wk Γ .back))
  ≡⟨⟩
    ⟦subT⟧ (SU.Fill m m<n) T .back ∘ MT.appₛ m m<n ⟦ _,_⊢_∶_.absₛ n T t ⊢t refl ⟧t
  ≡⟨⟩
    ⟦ ⟶→⊢ₗ (appₛ-absₛ n t m ⊢t m<n) ⟧t
  ∎
  )
interp (caseNat-zero T n z s x x₁ x₂) = ≈⁺ λ δ γ → refl
interp (caseNat-suc T n m i z s ⊢z ⊢s ⊢i n<⋆ m<n) = ≈⁺ λ δ γ → {!RG.≈→≡!}
interp (head-cons n i is x x₁ x₂) = ≈⁺ λ δ γ → ℕ≤-≡⁺ _ _ refl
interp {Γ = Γ} (tail-cons n i is m ⊢i ⊢is n<⋆ m<n) = ≈⁺ λ δ γ → Colist-≡⁺ λ k k≤m
  → ⟦ ⊢is ⟧t .feq _ (⟦ Γ ⟧Γ .eq-refl γ) _ _ _ _ _ _ _
interp (fix T t n ⊢t n<⋆) = {!!}
interp (cong-abs T t t′ p) = {!!}
interp (cong-appₗ t t′ u p x) = {!!}
interp (cong-appᵣ t u u′ x p) = {!!}
interp (cong-absₛ n t t′ p) = {!!}
interp (cong-appₛ p m<n) = {!!}
interp (cong-suc n m i i′ x x₁ x₂) = {!!}
interp (cong-cons₀ n i i′ is x x₁ x₂) = {!!}
interp (cong-cons₁ n i is is′ x x₁ x₂) = {!!}
interp (cong-head n is is′ x x₁) = {!!}
interp (cong-tail n m is is′ x x₁ x₂) = {!!}
interp (cong-caseNat₀ T n i i′ z s x x₁ x₂ x₃) = {!!}
interp (cong-caseNat₁ T n i z z′ s x x₁ x₂ x₃) = {!!}
interp (cong-caseNat₂ T n i z s s′ x x₁ x₂ x₃) = {!!}
interp (cong-fix T t t′ n n<⋆ p) = {!!}


-- -} --TODO
-- -} --TODO
-- -} --TODO
-- -} --TODO
