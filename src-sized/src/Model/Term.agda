{-# OPTIONS --without-K --allow-unsolved-metas #-} -- TODO
module Model.Term where

open import Cats.Category

open import Model.Size as MS using (_<_) renaming
  (⟦_⟧ΔRG to ⟦_⟧Δ ; ⟦_⟧nRG to ⟦_⟧n ; ⟦_⟧σRG to ⟦_⟧σ)
open import Model.Type as MT
open import Util.HoTT.Equiv
open import Util.Relation.Binary.PropositionalEquality using (happly)
open import Util.Prelude hiding (id ; _∘_ ; _×_)
open import Source.Size as SS using (v0 ; v1)
open import Source.Size.Substitution.Universe as SU using (sub-syntax-Size)
open import Source.Term
open import Source.Type as ST using (sub-syntax-Type ; sub-syntax-Ctx)

import Model.RGraph as RG

open Category._≅_
open MS.Size
open MS._<_
open MS._≤_
open RG._⇒_
open SS.Size
open ST.Ctx


⟦_⟧x : ∀ {Δ Γ x T}
  → Δ , Γ ⊢ₓ x ∶ T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T
⟦_⟧x {Γ = Γ ∙ T} zero = π₂ ⟦ Γ ⟧Γ
⟦ suc {U = U} x ⟧x = ⟦ x ⟧x ∘ π₁ ⟦ U ⟧T


⟦_⟧t : ∀ {Δ Γ t T}
  → Δ , Γ ⊢ t ∶ T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T
⟦ var x ⊢x ⟧t = ⟦ ⊢x ⟧x
⟦ abs {Γ = Γ} {U = U} T t ⊢t ⟧t
  = curry ⟦ Γ ⟧Γ ⟦ T ⟧T ⟦ U ⟧T ⟦ ⊢t ⟧t
⟦ app {T = T} {U = U} t u ⊢t ⊢u ⟧t
  = eval ⟦ T ⟧T ⟦ U ⟧T ∘ ⟨ ⟦ ⊢t ⟧t , ⟦ ⊢u ⟧t ⟩
⟦ absₛ {Γ = Γ} n T t ⊢t p ⟧t
  = MT.absₛ (⟦ ⊢t ⟧t ∘ ≡→≈⟦Type⟧Γ p .back ∘ ⟦subΓ⟧ SU.Wk Γ .back)
⟦ appₛ {Γ = Γ} {T = T} t m m<n ⊢t p ⟧t
  = ≡→≈⟦Type⟧T p .back ∘
    ⟦subT⟧ (SU.Fill m m<n) T .back ∘
    MT.appₛ m m<n ⟦ ⊢t ⟧t
⟦ zero n<⋆ ⟧t = record
  { fobj = λ γ → zero≤ _
  ; feq = λ δ≈δ′ x → refl
  }
⟦ suc n<⋆ m<n ⊢i ⟧t = record
  { fobj = λ γ → suc≤ _ _ (MS.⟦<⟧ m<n) (⟦ ⊢i ⟧t .fobj γ)
  ; feq = λ δ≈δ′ x → cong suc (⟦ ⊢i ⟧t .feq ⊤.tt x)
  }
⟦ cons n<⋆ ⊢i ⊢is ⟧t = record
  { fobj = λ γ → MT.cons (⟦ ⊢i ⟧t .fobj γ .proj₁) (⟦ ⊢is ⟧t .fobj γ .arr)
  ; feq = λ δ≈δ′ x a a₁ a₂ → {!Colist-≡⁺!}
  }
⟦ head n<⋆ ⊢is ⟧t = record
  { fobj = λ γ → MT.head (⟦ ⊢is ⟧t .fobj γ) , MS.<→≤ MS.nat<∞
  ; feq = λ δ≈δ′ x → ⟦ ⊢is ⟧t .feq ⊤.tt x 0 MS.0≤n MS.0≤n
  }
⟦ tail n<⋆ m<n ⊢is ⟧t = record
  { fobj = λ γ → MT.tail (⟦ ⊢is ⟧t .fobj γ) _ (MS.⟦<⟧ m<n)
  ; feq = λ δ≈δ′ x a a₁ a₂ → {!!}
  }
⟦ caseNat {T = T} n<⋆ ⊢i ⊢z ⊢s p ⟧t = record
  { fobj = λ γ → caseℕ≤ (⟦ ⊢i ⟧t .fobj γ) (⟦ ⊢z ⟧t .fobj γ)
      λ m m<n i
        → ⟦subT⟧ SU.Wk T .forth .fobj
            (≡→≈⟦Type⟧T p .forth .fobj (⟦ ⊢s ⟧t .fobj γ .arr m m<n .fobj i))
  ; feq = {!!}
  }
⟦ fix {n = n} {Γ} {T = T} n<⋆ ⊢t refl refl ⟧t
  = ⟦subT⟧ (SU.Fill n n<⋆) T .back ∘ term⇒
  module ⟦⟧t-fix where
    go
      : Σ[ f ∈ (∀ n n<⋆ δ → ⟦ Γ ⟧Γ .Obj δ → ⟦ T ⟧T .Obj (δ , n , n<⋆)) ]
        Σ[ f-param ∈ (∀ n n′ n<⋆ n′<⋆ δ δ′ (γ : ⟦ Γ ⟧Γ .Obj δ) (γ′ : ⟦ Γ ⟧Γ .Obj δ′)
          → ⟦ Γ ⟧Γ .eq _ γ γ′ → ⟦ T ⟧T .eq _ (f n n<⋆ δ γ) (f n′ n′<⋆ δ′ γ′)) ]
          (∀ {n} → f n ≡ _)
    go = MS.<-indΣ′
      (λ n → ∀ n<⋆ δ (γ : ⟦ Γ ⟧Γ .Obj δ) → ⟦ T ⟧T .Obj (δ , n , n<⋆))
      (λ n m f g → ∀ n<⋆ m<⋆ δ δ′ γ γ′ (γ≈γ′ : ⟦ Γ ⟧Γ .eq _ γ γ′)
        → ⟦ T ⟧T .eq _ (f n<⋆ δ γ) (g m<⋆ δ′ γ′))
      (λ n rec rec-resp n<⋆ δ γ
        → ⟦ ⊢t ⟧t .fobj γ .arr n n<⋆ .fobj
            (⟦∀⟧′-resp-≈⟦Type⟧ (⟦subT⟧ SU.Skip T) .back record
              { arr = λ m m<n → rec m m<n (MS.<-trans m<n n<⋆) δ γ
              ; param = λ m m<n m′ m′<n
                  → rec-resp m m<n m′ m′<n _ _ δ δ γ γ (⟦ Γ ⟧Γ .eq-refl γ)
              }))
      λ n g g-resp m h h-resp g≈h n<⋆ m<⋆ δ δ′ γ γ′ γ≈γ′
        → ⟦ ⊢t ⟧t .feq _ γ≈γ′ n n<⋆ m m<⋆ λ k k<n k′ k′<m
            → ⟦subT⟧ SU.Skip T .back .feq _
                (g≈h k k<n k′ k′<m _ _ δ δ′ γ γ′ γ≈γ′)

    term : ∀ n n<⋆ δ → ⟦ Γ ⟧Γ .Obj δ → ⟦ T ⟧T .Obj (δ , n , n<⋆)
    term = go .proj₁

    term-param : ∀ n n′ n<⋆ n′<⋆ δ δ′ (γ : ⟦ Γ ⟧Γ .Obj δ) (γ′ : ⟦ Γ ⟧Γ .Obj δ′)
      → ⟦ Γ ⟧Γ .eq _ γ γ′
      → ⟦ T ⟧T .eq _ (term n n<⋆ δ γ) (term n′ n′<⋆ δ′ γ′)
    term-param = go .proj₂ .proj₁

    term-unfold₀ : ∀ {n}
      → term n
      ≡ λ n<⋆ δ γ → ⟦ ⊢t ⟧t .fobj γ .arr n n<⋆ .fobj
            (⟦∀⟧′-resp-≈⟦Type⟧ (⟦subT⟧ SU.Skip T) .back record
              { arr = λ m m<n → term m (MS.<-trans m<n n<⋆) δ γ
              ; param = λ m m<n m′ m′<n
                  → term-param _ _ _ _ _ _ _ _ (⟦ Γ ⟧Γ .eq-refl γ)
              })
    term-unfold₀ = go .proj₂ .proj₂

    term-unfold : ∀ {n n<⋆ δ γ}
      → term n n<⋆ δ γ
      ≡ ⟦ ⊢t ⟧t .fobj γ .arr n n<⋆ .fobj
          (⟦∀⟧′-resp-≈⟦Type⟧ (⟦subT⟧ SU.Skip T) .back record
            { arr = λ m m<n → term m (MS.<-trans m<n n<⋆) δ γ
            ; param = λ m m<n m′ m′<n
                → term-param _ _ _ _ _ _ _ _ (⟦ Γ ⟧Γ .eq-refl γ)
            })
    term-unfold {n} {n<⋆} {δ} {γ} = cong (λ f → f n<⋆ δ γ) term-unfold₀

    term⇒ : ⟦ Γ ⟧Γ ⇒ subT ⟦ SU.Fill n n<⋆ ⟧σ ⟦ T ⟧T
    term⇒ = record
      { fobj = term _ _ _
      ; feq = λ δ≈δ′ → term-param _ _ _ _ _ _ _ _
      }


⟦_⟧ν : ∀ {Δ} {Γ Ψ : ST.Ctx Δ} (ν : Sub Γ Ψ) → ⟦ Γ ⟧Γ ⇒ ⟦ Ψ ⟧Γ
⟦ [] ⟧ν = ! _
⟦ snoc ν t ⊢t ⟧ν = ⟨ ⟦ ν ⟧ν , ⟦ ⊢t ⟧t ⟩


⟦cast⊢Γ⟧ : ∀ {Δ Γ Ψ t T}
  → (p : Γ ≡ Ψ)
  → (⊢t : Δ , Γ ⊢ t ∶ T)
  → ⟦ cast⊢Γ p ⊢t ⟧t ≈ ⟦ ⊢t ⟧t ∘ ≡→≈⟦Type⟧ (cong ⟦_⟧Γ p) .back
⟦cast⊢Γ⟧ refl ⊢t = ≈⁺ (λ δ x → refl)


⟦sub⟧ : ∀ {Δ Γ Ψ t T}
  → (ν : Sub Γ Ψ)
  → (⊢t : Δ , Ψ ⊢ t ∶ T)
  → ⟦ sub-resp-⊢ ν ⊢t ⟧t ≈ ⟦ ⊢t ⟧t ∘ ⟦ ν ⟧ν
⟦sub⟧ ν (var x x₁) = {!!}
⟦sub⟧ ν (abs T t ⊢t) = {!!}
⟦sub⟧ ν (app t u ⊢t ⊢u) = {!!}
⟦sub⟧ ν (_,_⊢_∶_.absₛ n T t ⊢t refl) = {!!}
⟦sub⟧ ν (_,_⊢_∶_.appₛ t m m<n ⊢t refl) = {!!}
⟦sub⟧ ν (zero x) = ≈⁺ λ _ _ → refl
⟦sub⟧ ν (suc x x₁ ⊢t) = ≈⁺ λ _ _ → {!!}
⟦sub⟧ ν (_,_⊢_∶_.cons x ⊢t ⊢u) = {!!}
⟦sub⟧ ν (_,_⊢_∶_.head x ⊢t) = {!!}
⟦sub⟧ ν (_,_⊢_∶_.tail x x₁ ⊢t) = {!!}
⟦sub⟧ ν (caseNat x ⊢t ⊢t₁ ⊢t₂ x₁) = {!!}
⟦sub⟧ ν (fix n<⋆ ⊢t x x₁) = {!!}


⟦subₛ⟧ : ∀ {Δ Ω Γ t T}
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
