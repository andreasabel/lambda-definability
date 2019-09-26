{-# OPTIONS --without-K --allow-unsolved-metas #-} -- TODO
module Model.Term where

open import Cats.Category

open import Model.Size as MS using (_<_) renaming
  (⟦_⟧ΔRG to ⟦_⟧Δ ; ⟦_⟧nRG to ⟦_⟧n ; ⟦_⟧σRG to ⟦_⟧σ)
open import Model.Type as MT
open import Util.Relation.Binary.PropositionalEquality using (cast)
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
⟦ fix {n = n} {Γ} {T = T} n<⋆ ⊢t refl refl ⟧t = record
  { fobj = λ {δ} γ
      → ⟦subT⟧ (SU.Fill n n<⋆) T .back .fobj
          (term .proj₁ (⟦ n ⟧n .fobj δ) (MS.⟦<⟧ n<⋆) δ γ)
  ; feq = λ {δ} {δ′} δ≈δ′ {γ} {γ′} γ≈γ′
      → ⟦subT⟧ (SU.Fill n n<⋆) T .back .feq _
          (term .proj₂ (⟦ n ⟧n .fobj δ) (⟦ n ⟧n .fobj δ′) (MS.⟦<⟧ n<⋆)
            (MS.⟦<⟧ n<⋆) δ δ′ γ γ′ γ≈γ′)
  }
  module ⟦⟧-fix where
    term = MS.<-indΣ
      (λ n → ∀ n<⋆ δ (γ : ⟦ Γ ⟧Γ .Obj δ) → ⟦ T ⟧T .Obj (δ , n , n<⋆))
      (λ n m f g → ∀ n<⋆ m<⋆ δ δ′ γ γ′ (γ≈γ′ : ⟦ Γ ⟧Γ .eq _ γ γ′)
        → ⟦ T ⟧T .eq _ (f n<⋆ δ γ) (g m<⋆ δ′ γ′))
      (λ n rec rec-resp n<⋆ δ γ
        → ⟦ ⊢t ⟧t .fobj γ .arr n n<⋆ .fobj record
            { arr = λ m m<n
                → ⟦subT⟧ SU.Skip T .back .fobj
                    (rec m m<n (MS.<-trans m<n n<⋆) δ γ)
            ; param = λ m m<n m′ m′<n
                → ⟦subT⟧ SU.Skip T .back .feq _
                    (rec-resp m m<n m′ m′<n _ _ δ δ γ γ (⟦ Γ ⟧Γ .eq-refl _))
            })
      λ n g g-resp m h h-resp g≈h n<⋆ m<⋆ δ δ′ γ γ′ γ≈γ′
        → ⟦ ⊢t ⟧t .feq _ γ≈γ′ n n<⋆ m m<⋆ λ k k<n k′ k′<m
            → ⟦subT⟧ SU.Skip T .back .feq _
                (g≈h k k<n k′ k′<m _ _ δ δ′ γ γ′ γ≈γ′)
