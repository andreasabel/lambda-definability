{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

module Container where

open import Library

open import Function.Surjection using (Surjection; Surjective)
open import Function.Bijection using (Bijection; Bijective)
open import Function.Equality  using (Π)

open import Relation.Binary.PropositionalEquality using (setoid; Extensionality)

_≅_ : (A B : Set) → Set
A ≅ B = Bijection (setoid A) (setoid B)

open Bijection; open Bijective
-- open Surjection -- ; open Surjective

record Cont (I : Set) : Set₁ where
  constructor _▷_ ; field
    S : Set
    P : S → I → Set
open Cont

⟦_⟧ : ∀{I} → Cont I → (I → Set) → Set
⟦ S ▷ P ⟧ ρ = Σ S λ s → ∀ i → P s i → ρ i

Const : (A : Set) → ∀{I} → Cont I
Const A = A ▷ λ _ _ → ⊥

den-Const : ∀ A {I ρ} → ⟦ Const A {I} ⟧ ρ ≅ A
den-Const A .to .Π._⟨$⟩_ = proj₁
den-Const A .to .Π.cong refl = refl
den-Const A .bijective .injective {a , f} {.a , f'} refl = cong (a ,_) (funExt λ i → funExt λ())
den-Const A .bijective .surjective .Surjective.from Π.⟨$⟩ x = x , λ i ()
den-Const A .bijective .surjective .Surjective.from .Π.cong refl = refl
den-Const A .bijective .surjective .Surjective.right-inverse-of a = refl

Var : ∀{n} (i : Fin n) → Cont (Fin n)
Var i = ⊤ ▷ λ _ j → δ i j

den-Var : ∀{n} (i : Fin n) {ρ} → ⟦ Var i ⟧ ρ ≅ ρ i
den-Var i .to Π.⟨$⟩ (_ , f) = f i _
den-Var i .to .Π.cong refl = refl
den-Var i {ρ} .bijective .injective  {⊤.tt , f} {⊤.tt , f'} p = cong (_ ,_) (funExt  λ j →  funExt λ x → {!aux f  f' p j (i ≟ j) x!}  )
  -- where
  -- aux : ∀ (f f' : ∀ j → True (i ≟ j) → ρ j) (p : f i _ ≡ f i _) j (i≟j : Dec (i ≡ j)) (x : True i≟j) → f j x ≡ f' j x
  -- aux f f' p j (yes refl) ⊤.tt = p
  -- aux f f' p j (no ¬p) ()

den-Var {n} i {ρ} .bijective .surjective .Surjective.from Π.⟨$⟩ x = _ , λ j p → {!aux j p x !}
  where
  aux : ∀ (j : Fin n) → δ i j → ρ i → ρ j
  aux j x with i ≟ j
  aux j x | yes refl = id
  aux j () | no ¬p
den-Var i .bijective .surjective .Surjective.from .Π.cong x = {!!}
den-Var i .bijective .surjective .Surjective.right-inverse-of x = {!!}

-- -}
