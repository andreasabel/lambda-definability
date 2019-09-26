{-# OPTIONS --without-K #-}
module Model.Reduction where

open import Cats.Category

open import Model.Size using () renaming (⟦_⟧σRG to ⟦_⟧σ)
open import Model.Term
open import Model.Type as MT
open import Source.Reduction
open import Source.Term
open import Source.Type as ST using (sub-syntax-Ctx ; sub-syntax-Type)
open import Util.Prelude renaming (_∘_ to _∘F_)
open import Util.Relation.Binary.PropositionalEquality using (happly ; ×-≡⁺)

import Model.RGraph as RG
import Source.Size as SS
import Source.Size.Substitution.Canonical as SC
import Source.Size.Substitution.Universe as SU

open Category._≅_

open SS.Ctx


-- TODO remove
import Cats.Category.Constructions.Iso as Iso
open Iso.Iso



⟦subₛ⟧
  : ∀ {Δ Ω Γ t T}
  → (σ : SU.Sub Δ Ω)
  → (⊢t : Ω , Γ ⊢ t ∶ T)
  → ⟦ subₛ-resp-⊢ σ ⊢t ⟧t ≈ MT.subₛ Γ T σ ⟦ ⊢t ⟧t
⟦subₛ⟧ σ (var x ⊢x) = {!!}
⟦subₛ⟧ σ (abs T t ⊢t)
  = ≈⁺ λ δ γ → RG.≈→≡ (RG.≈⁺ λ x → ⟦subₛ⟧ σ ⊢t .≈⁻ δ (γ , x))
⟦subₛ⟧ σ (app {Γ = Γ} {T = T} {U = U} t u ⊢t ⊢u) = ≈⁺ λ δ γ
  → let open ≡-Reasoning in
    begin
      ⟦ subₛ-resp-⊢ σ ⊢t ⟧t .fobj γ .RG.fobj
        (⟦ subₛ-resp-⊢ σ ⊢u ⟧t .fobj γ)
    ≡⟨ cong (λ f → f .RG.fobj (⟦ subₛ-resp-⊢ σ ⊢u ⟧t .fobj γ))
        (⟦subₛ⟧ σ ⊢t .≈⁻ δ γ) ⟩
      MT.subₛ Γ (T ST.⇒ U) σ ⟦ ⊢t ⟧t .fobj γ .RG.fobj
        (⟦ subₛ-resp-⊢ σ ⊢u ⟧t .fobj γ)
    ≡⟨ cong (MT.subₛ Γ (T ST.⇒ U) σ ⟦ ⊢t ⟧t .fobj γ .RG.fobj)
        (⟦subₛ⟧ σ ⊢u .≈⁻ δ γ) ⟩
      MT.subₛ Γ (T ST.⇒ U) σ ⟦ ⊢t ⟧t .fobj γ .RG.fobj
        (MT.subₛ Γ T σ ⟦ ⊢u ⟧t .fobj γ)
    ≡⟨ {!!} ⟩
      ⟦subT⟧ σ U .back .fobj
        (⟦ ⊢t ⟧t .fobj (⟦subΓ⟧ σ Γ .forth .fobj γ) .RG.fobj
         (⟦ ⊢u ⟧t .fobj (⟦subΓ⟧ σ Γ .forth .fobj γ)))
    ∎
⟦subₛ⟧ σ (absₛ {Γ = Γ} n T t ⊢t refl) = ≈⁺ λ δ x
  → ⟦∀⟧′-≡⁺ _ _ λ m m<n
      → trans (⟦subₛ⟧ (SU.Keep′ σ) ⊢t .≈⁻ _ _)
          (cong (⟦subT⟧ (SU.Keep′ σ) T .back .fobj) {!!})
  -- = let open ≈-Reasoning in
  --   begin
  --     ⟦ subₛ-resp-⊢ σ (_,_⊢_∶_.absₛ n T t ⊢t p) ⟧t
  --     -- MT.absₛ
  --     -- (⟦ subₛ-resp-⊢ (SU.Keep′ σ) ⊢t ⟧t ∘
  --     --  ≡→≈⟦Type⟧Γ (subₛ-resp-⊢-absₛ.eq n t T σ ⊢t p) .back ∘
  --     --  ⟦subΓ⟧ SU.Wk (Γ [ σ ]Γ) .back)
  --   ≈⟨ cong (λ f → MT.absₛ (f ∘ ≡→≈⟦Type⟧Γ (subₛ-resp-⊢-absₛ.eq n t T σ ⊢t p) .back ∘
  --      ⟦subΓ⟧ SU.Wk (sub-syntax-Ctx σ Γ) .back)) ? ⟩
  --     ?
  --   ≈⟨ {!!} ⟩
  --     MT.subₛ Γ (ST.Π n , T) σ
  --       (MT.absₛ (⟦ ⊢t ⟧t ∘ ≡→≈⟦Type⟧Γ p .back ∘ ⟦subΓ⟧ SU.Wk Γ .back))
  --   ∎
-- ⟦subₛ⟧ σ (absₛ n T t ⊢t p) = ≈⁺ λ δ γ → ⟦∀⟧′-≡⁺ _ _ λ m m<n
--   → trans (⟦subₛ⟧ (SU.Keep′ σ) ⊢t .≈⁻ _ _) {!!}
⟦subₛ⟧ σ (appₛ t m m<n ⊢t x) = {!!}
⟦subₛ⟧ σ (zero x) = ≈⁺ λ δ γ → ℕ≤-≡⁺ _ _ refl
⟦subₛ⟧ σ (suc {Γ = Γ} x x₁ ⊢t) = ≈⁺ λ δ γ → ℕ≤-≡⁺ _ _
  (cong suc (cong proj₁ (⟦subₛ⟧ σ ⊢t .≈⁻ δ γ)))
⟦subₛ⟧ σ (cons x ⊢i ⊢is) = ≈⁺ λ δ γ → Colist-≡⁺ λ m m≤n → {!!}
⟦subₛ⟧ σ (head x ⊢t) = {!!}
⟦subₛ⟧ σ (tail x x₁ ⊢t) = {!!}
⟦subₛ⟧ σ (caseNat x ⊢t ⊢t₁ ⊢t₂ x₁) = ≈⁺ λ δ γ
  → {!!}
⟦subₛ⟧ σ (fix n<⋆ ⊢t x x₁) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (var x x₁) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (abs T t ⊢t) = ≈↝⁺ λ γ x → RGraphMor-≡⁺ λ γ₁
--   → ⟦subₛ-resp-⊢⟧ σ ⊢t .≈↝⁻ γ (x , γ₁)
-- ⟦subₛ-resp-⊢⟧ {Γ = Γ} {T = T} σ (app t u ⊢t ⊢u) = ≈↝⁺ λ γ x
--   -- → {!⟦subₛ-resp-⊢⟧ σ ⊢u!}
--   → trans
--       (cong (λ y → ⟦ subₛ-resp-⊢ σ ⊢t ⟧t .fObj x .fObj y)
--         (⟦subₛ-resp-⊢⟧ σ ⊢u .≈↝⁻ γ x))
--       -- {!cong (λ u → u .fObj (⟦subₛ⟧ Γ T σ ⟦ ⊢u ⟧t .fObj x)) (⟦subₛ-resp-⊢⟧ σ ⊢t .≈↝⁻ ? ?)!}
--       (trans (cong (λ u → u .fObj _) (⟦subₛ-resp-⊢⟧ σ ⊢t .≈↝⁻ γ x)) {!!})
-- ⟦subₛ-resp-⊢⟧ σ (absₛ n T t ⊢t) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (appₛ t m m<n ⊢t) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ zero = ≈↝⁺ λ γ x → ⟦∀⟧′-≡⁺ _ _ λ m m<n → ℕ≤-≡⁺ _ _ {!proj₁-!}
-- ⟦subₛ-resp-⊢⟧ σ suc = ≈↝⁺ λ γ x → ⟦∀⟧′-≡⁺ _ _ λ n n<⋆ → ⟦∀⟧′-≡⁺ _ _ λ m m<n
--   → RGraphMor-≡⁺ λ γ₁ → ℕ≤-≡⁺ _ _ {!!}
-- ⟦subₛ-resp-⊢⟧ σ _,_⊢_∶_.cons = ≈↝⁺ λ γ x → ⟦∀⟧′-≡⁺ _ _ λ m m<n → RGraphMor-≡⁺ λ γ₁ → RGraphMor-≡⁺ λ γ₂ → {!!}
-- ⟦subₛ-resp-⊢⟧ σ _,_⊢_∶_.head = {!!}
-- ⟦subₛ-resp-⊢⟧ σ _,_⊢_∶_.tail = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (caseNat T) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (fix T) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (cast⊢ x x₁ ⊢t) = {!!}


⟦cast⊢Γ⟧ : ∀ {Δ Γ Ψ t T}
  → (p : Γ ≡ Ψ)
  → (⊢t : Δ , Γ ⊢ t ∶ T)
  → ⟦ cast⊢Γ p ⊢t ⟧t ≈ ⟦ ⊢t ⟧t ∘ ≡→≈⟦Type⟧ (cong ⟦_⟧Γ p) .back
⟦cast⊢Γ⟧ refl ⊢t = ≈⁺ (λ δ x → refl)


⟦subΓ⟧∘≡→≈⟦Type⟧ : ∀ {Δ Ω} {σ : SU.Sub Δ Ω} {Γ : ST.Ctx Δ} {Ψ : ST.Ctx Ω}
  → (p : Γ ≡ Ψ [ σ ]Γ)
  → ⟦subΓ⟧ σ Ψ .forth ∘ ≡→≈⟦Type⟧ (cong ⟦_⟧Γ p) .forth ≈ {!!}
⟦subΓ⟧∘≡→≈⟦Type⟧ = {!!}


lem₀ : (p : Γ ≡ Γ [ σ ]Γ [ τ ]Γ)


interp : ∀ {Δ Γ t u T}
  → (p : Δ , Γ ⊢ t ⟶ u ∶ T)
  → ⟦ ⟶→⊢ₗ p ⟧t ≈ ⟦ ⟶→⊢ᵣ p ⟧t
interp (app-abs t u x ⊢u) = {!!}
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
  ≈⟨ {!!} ⟩
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
-- interp {Δ} {Γ} (appₛ-absₛ n {T = T} t m ⊢t m<n) = ≈⁺ λ δ γ →
--   let open ≡-Reasoning in sym (
--   begin
--     ⟦ cast⊢Γ (⟶→⊢ᵣ.eq n m t m<n ⊢t) (subₛ-resp-⊢ (SU.Fill m m<n) ⊢t) ⟧t .fobj γ
--   ≡⟨ ⟦cast⊢Γ⟧ (⟶→⊢ᵣ.eq n m t m<n ⊢t) (subₛ-resp-⊢ (SU.Fill m m<n) ⊢t) .≈⁻ δ γ ⟩
--     ⟦ subₛ-resp-⊢ (SU.Fill m m<n) ⊢t ⟧t .fobj
--       (≡→≈⟦Type⟧ (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq n m t m<n ⊢t)) .back .fobj γ)
--   ≡⟨ ⟦subₛ⟧ (SU.Fill m m<n) ⊢t .≈⁻ _ _ ⟩
--     MT.subₛ (Γ [ SU.Wk ]Γ) T (SU.Fill m m<n) ⟦ ⊢t ⟧t .fobj
--       (≡→≈⟦Type⟧ (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq n m t m<n ⊢t)) .back .fobj γ)
--   ≡⟨⟩
--     ⟦subT⟧ (SU.Fill m m<n) T .back .fobj
--       (⟦ ⊢t ⟧t .fobj
--         (⟦subΓ⟧ (SU.Fill m m<n) (ST.subΓ SU.Wk Γ) .forth .fobj
--         (castObj (sym (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq n m t m<n ⊢t))) γ)))
--   ≡⟨ cong (λ x → ⟦subT⟧ (SU.Fill m m<n) T .back .fobj (⟦ ⊢t ⟧t .fobj x))
--       (go₁ Γ δ γ _) ⟩
--     ⟦subT⟧ (SU.Fill m m<n) T .back .fobj
--       (⟦ ⊢t ⟧t .fobj (⟦subΓ⟧ SU.Wk Γ .back .fobj γ))
--   ∎)
--   where
--     go₀ : ∀ T δ (γ : ⟦ T ⟧T .Obj δ)
--       → (p : T [ SU.Wk ]T [ SU.Fill m m<n ]T ≡ T)
--       → ⟦subT⟧ (SU.Fill m m<n) (T [ SU.Wk ]T) .forth .fobj
--           (≡→≈⟦Type⟧ (cong ⟦_⟧T p) .back .fobj γ)
--       ≡ ⟦subT⟧ SU.Wk T .back .fobj γ
--     go₀ (ST.Nat n) δ γ p = ℕ≤-≡⁺ _ _ {!!}
--     go₀ (ST.Stream n) δ γ p = Colist-≡⁺ λ m m≤n → {!!}
--     go₀ (T ST.⇒ U) δ γ p = RG.≈→≡ (RG.≈⁺ λ x
--       → {!trans (go₀ U δ (γ .RG.fobj ?) ?) ?!})
--       -- → trans
--       --     (cong (λ f → f .RG.fobj (⟦subT⟧ (SU.Fill m m<n) (ST.sub SU.Wk T) .back .fobj x))
--       --       {!go₀ U δ ? ?!})
--       --     {!!})
--     go₀ (ST.Π n , T) δ γ p = ⟦∀⟧′-≡⁺ _ _ λ m m<n → {!!}
--     -- Need a stronger IH here: SU.Keep′ SU.Wk and SU.Keep′ (SU.Fill m m<n).

--     go₁ : ∀ Γ δ (γ : ⟦ Γ ⟧Γ .Obj δ)
--       → (p : Γ [ SU.Wk ]Γ [ SU.Fill m m<n ]Γ ≡ Γ)
--       → ⟦subΓ⟧ (SU.Fill m m<n) (Γ [ SU.Wk ]Γ) .forth .fobj
--           (≡→≈⟦Type⟧ (cong ⟦_⟧Γ p) .back .fobj γ)
--       ≡ ⟦subΓ⟧ SU.Wk Γ .back .fobj γ
--     go₁ ST.[] δ γ refl = refl
--     go₁ (Γ ST.∙ T) δ (γ , t) p = ×-≡⁺ ({!trans (go₁ Γ δ (proj₁ γ) ?) ?!} , {!!})
interp (caseNat-zero T n z s x x₁ x₂) = ≈⁺ λ δ γ → refl
interp (caseNat-suc T n m i z s ⊢z ⊢s ⊢i n<⋆ m<n) = ≈⁺ λ δ γ → {!RG.≈→≡!}
interp (head-cons n i is x x₁ x₂) = ≈⁺ λ δ γ → ℕ≤-≡⁺ _ _ refl
interp {Γ = Γ} (tail-cons n i is m ⊢i ⊢is n<⋆ m<n) = ≈⁺ λ δ γ → Colist-≡⁺ λ k k≤m
  → ⟦ ⊢is ⟧t .feq _ (⟦ Γ ⟧Γ .eq-refl γ) _ _ _ _ _ _ _
interp (fix T t n x n<⋆) = ≈⁺ (λ δ x₁ → {!!})
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


{-
interp (app-abs t u x ⊢u) = ≈⁺ (λ γ x₁ → {!!})
-- interp {Δ} {Γ} (appₛ-absₛ n {T = T} t m ⊢t m<n) =
--   let open ≈-Reasoning in ≈-sym (
--   begin
--     ⟦ ⟶→⊢ᵣ (appₛ-absₛ n t m ⊢t m<n) ⟧t
--   ≡⟨⟩
--     ⟦ cast⊢Γ (⟶→⊢ᵣ.eq₀ n m t m<n ⊢t) (subₛ-resp-⊢ (SU.Fill m m<n) ⊢t) ⟧t
--   ≡⟨⟩
--     ⟦ subₛ-resp-⊢ (SU.Fill m m<n) ⊢t ⟧t ∘
--     ≡→≈⟦Type⟧ (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq₀ n m t m<n ⊢t)) .back
--   ≈⟨ {!!} ⟩
--     MT.subₛ (Γ [ SU.Wk ]Γ) T (SU.Fill m m<n) ⟦ ⊢t ⟧t ∘
--     ≡→≈⟦Type⟧ (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq₀ n m t m<n ⊢t)) .back
--   ≈⟨ {!!} ⟩
--     ⟦subT⟧ (SU.Fill m m<n) T .back ∘
--     subt ⟦ SU.Fill m m<n ⟧σ (⟦ ⊢t ⟧t ∘ ⟦subΓ⟧ SU.Wk Γ .back)
--   ≈⟨ ⟦Types⟧.∘-resp-r {f = ⟦subT⟧ (SU.Fill m m<n) T .back} (≈-sym (appₛ∘absₛ m m<n (⟦ ⊢t ⟧t ∘ ⟦subΓ⟧ SU.Wk Γ .back))) ⟩
--     ⟦subT⟧ (SU.Fill m m<n) T .back ∘
--     MT.appₛ m m<n (MT.absₛ (⟦ ⊢t ⟧t ∘ ⟦subΓ⟧ SU.Wk Γ .back))
--   ≡⟨⟩
--     ⟦subT⟧ (SU.Fill m m<n) T .back ∘ MT.appₛ m m<n ⟦ _,_⊢_∶_.absₛ n T t ⊢t ⟧t
--   ≡⟨⟩
--     ⟦ ⟶→⊢ₗ (appₛ-absₛ n t m ⊢t m<n) ⟧t
--   ∎
--   )
interp {Δ} {Γ} (appₛ-absₛ n {T = T} t m ⊢t m<n) = ≈⁺ λ δ x
  → let open ≡-Reasoning in sym (
    begin
      ⟦ subₛ-resp-⊢ (SU.Fill m m<n) ⊢t ⟧t .fobj
        (subst (λ T → Obj T δ) (sym (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq₀ n m t m<n ⊢t))) x)
    ≡⟨ ⟦subₛ⟧ (SU.Fill m m<n) ⊢t .≈⁻ _ _ ⟩
      MT.subₛ (Γ [ SU.Wk ]Γ) T (SU.Fill m m<n) ⟦ ⊢t ⟧t .fobj
        (subst (λ T → Obj T δ) (sym (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq₀ n m t m<n ⊢t))) x)
    ≡⟨⟩
      ⟦subT⟧ (SU.Fill m m<n) T .back .fobj
        (⟦ ⊢t ⟧t .fobj
         (⟦subΓ⟧ (SU.Fill m m<n) (ST.subΓ SU.Wk Γ) .forth .fobj
          (subst (λ T → Obj T δ)
           (sym (cong ⟦_⟧Γ (⟶→⊢ᵣ.eq₀ n m t m<n ⊢t))) x)))
    ≡⟨ cong (⟦subT⟧ (SU.Fill m m<n) T .back .fobj ∘F ⟦ ⊢t ⟧t .fobj)
         (go₁ Γ δ x (⟶→⊢ᵣ.eq₀ n m t m<n ⊢t)) ⟩
      ⟦subT⟧ (SU.Fill m m<n) T .back .fobj
        (⟦ ⊢t ⟧t .fobj
          (⟦subΓ⟧ SU.Wk Γ .back .fobj x))
    ∎)
  where
    go₀ : ∀ T δ x
      → (p : T [ SU.Wk ]T [ SU.Fill m m<n ]T ≡ T)
      → ⟦subT⟧ (SU.Fill m m<n) (ST.sub SU.Wk T) .forth .fobj
          (subst (λ T → (Obj T δ)) (sym (cong ⟦_⟧T p)) x)
      ≡ ⟦subT⟧ SU.Wk T .back .fobj x
    go₀ (ST.Nat n) δ x p = {!p!}
    go₀ (ST.Stream n) δ x p = Colist-≡⁺ λ k k≤n → {!!}
    go₀ (T ST.⇒ T₁) δ x p = {!≈→≡ ?!}
    go₀ (ST.Π n , T) δ x p = ⟦∀⟧′-≡⁺ _ _ λ k k<n → {!!}

    go₁ : ∀ Γ δ x
      → (p : Γ [ SU.Wk ]Γ [ SU.Fill m m<n ]Γ ≡ Γ)
      → ⟦subΓ⟧ (SU.Fill m m<n) (ST.subΓ SU.Wk Γ) .forth .fobj
          (subst (λ T → (Obj T δ)) (sym (cong ⟦_⟧Γ p)) x)
      ≡ ⟦subΓ⟧ SU.Wk Γ .back .fobj x
    go₁ ST.[] δ x refl = refl
    go₁ (Γ ST.∙ T) δ (x , y) p = ×-≡⁺ ({!go Γ δ x ?!} , {!!})
interp (caseNat-zero T n z s ⊢z ⊢s n<⋆) = ≈⁺ λ δ x → {!!}
interp (caseNat-suc T n m i z s x x₁ x₂ x₃ x₄) = {!!}
interp (head-cons n i is x x₁ x₂) = ≈⁺ (λ γ x₃ → ℕ≤-≡⁺ _ _ refl)
interp (tail-cons n i is m x x₁ x₂ x₃) = ≈⁺ (λ γ x₄ → ⟦∀⟧′-≡⁺ _ _ λ m₁ m<n → Colist-≡⁺ (λ m₂ m≤n → {!!}))
interp (fix T t n x n<⋆) = {!!}
interp (cong-abs T t t′ p) = {!!}
interp (cong-appₗ t t′ u p x) = {!!}
interp (cong-appᵣ t u u′ x p) = {!!}
interp (cong-absₛ n t t′ p) = {!!}
interp (cong-appₛ p m<n) = {!!}
-}
