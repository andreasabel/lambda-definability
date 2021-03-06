{-# OPTIONS --without-K --safe #-}
module Util.HoTT.HLevel.Core where

open import Data.Nat using (_+_)
open import Level using (Lift ; lift ; lower)

open import Util.Prelude
open import Util.Relation.Binary.LogicalEquivalence using (_↔_ ; forth ; back)
open import Util.Relation.Binary.PropositionalEquality using
  ( Σ-≡⁺ ; Σ-≡⁻ ; Σ-≡⁺∘Σ-≡⁻ ; trans-injectiveˡ )


private
  variable
    α β γ : Level
    A B C : Set α


IsContr : Set α → Set α
IsContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)


IsProp : Set α → Set α
IsProp A = (x y : A) → x ≡ y


IsProp′ : Set α → Set α
IsProp′ A = (x y : A) → IsContr (x ≡ y)


IsProp→IsProp′ : IsProp A → IsProp′ A
IsProp→IsProp′ {A = A} A-prop x y = (A-prop x y) , canon
  where
    go : (p : x ≡ y) → trans p (A-prop y y) ≡ A-prop x y
    go refl = refl

    canon : (p : x ≡ y) → A-prop x y ≡ p
    canon refl = trans-injectiveˡ (A-prop y y) (go (A-prop y y))


IsProp′→IsProp : IsProp′ A → IsProp A
IsProp′→IsProp A-prop x y = proj₁ (A-prop x y)


IsProp↔IsProp′ : IsProp A ↔ IsProp′ A
IsProp↔IsProp′ .forth = IsProp→IsProp′
IsProp↔IsProp′ .back = IsProp′→IsProp


IsSet : Set α → Set α
IsSet A = {x y : A} → IsProp (x ≡ y)


IsOfHLevel : ℕ → Set α → Set α
IsOfHLevel 0 A = IsContr A
IsOfHLevel 1 A = IsProp A
IsOfHLevel (suc (suc n)) A = {x y : A} → IsOfHLevel (suc n) (x ≡ y)


IsOfHLevel′ : ℕ → Set α → Set α
IsOfHLevel′ zero A = IsContr A
IsOfHLevel′ (suc n) A = ∀ {x y : A} → IsOfHLevel′ n (x ≡ y)


IsOfHLevel′→IsOfHLevel : ∀ n → IsOfHLevel′ n A → IsOfHLevel n A
IsOfHLevel′→IsOfHLevel zero A-contr = A-contr
IsOfHLevel′→IsOfHLevel (suc zero) A-prop = IsProp′→IsProp λ _ _ → A-prop
IsOfHLevel′→IsOfHLevel (suc (suc n)) A-level
  = IsOfHLevel′→IsOfHLevel (suc n) A-level


IsOfHLevel→IsOfHLevel′ : ∀ n → IsOfHLevel n A → IsOfHLevel′ n A
IsOfHLevel→IsOfHLevel′ zero A-contr = A-contr
IsOfHLevel→IsOfHLevel′ (suc zero) A-prop = IsProp→IsProp′ A-prop _ _
IsOfHLevel→IsOfHLevel′ (suc (suc n)) A-level
  = IsOfHLevel→IsOfHLevel′ (suc n) A-level


IsOfHLevel↔IsOfHLevel′ : ∀ n → IsOfHLevel n A ↔ IsOfHLevel′ n A
IsOfHLevel↔IsOfHLevel′ n .forth = IsOfHLevel→IsOfHLevel′ n
IsOfHLevel↔IsOfHLevel′ n .back = IsOfHLevel′→IsOfHLevel n


IsContr→IsProp : IsContr A → IsProp A
IsContr→IsProp (c , c-canon) x y = trans (sym (c-canon x)) (c-canon y)


IsOfHLevel-suc : ∀ n → IsOfHLevel n A → IsOfHLevel (suc n) A
IsOfHLevel-suc 0 A-contr = IsContr→IsProp A-contr
IsOfHLevel-suc 1 A-prop = IsOfHLevel-suc 0 (IsProp→IsProp′ A-prop _ _)
IsOfHLevel-suc (suc (suc n)) A-level-n = IsOfHLevel-suc (suc n) A-level-n


IsOfHLevel-suc-n : ∀ n m → IsOfHLevel n A → IsOfHLevel (m + n) A
IsOfHLevel-suc-n {A = A} n zero A-level = A-level
IsOfHLevel-suc-n n (suc m) A-level
  = IsOfHLevel-suc (m + n) (IsOfHLevel-suc-n n m A-level)


IsProp→IsSet : IsProp A → IsSet A
IsProp→IsSet = IsOfHLevel-suc 1


IsContr→IsSet : IsContr A → IsSet A
IsContr→IsSet = IsOfHLevel-suc-n 0 2


record HLevel α n : Set (lsuc α) where
  constructor HLevel⁺
  field
    type : Set α
    level : IsOfHLevel n type

open HLevel public


HContr : ∀ α → Set (lsuc α)
HContr α = HLevel α 0


HProp : ∀ α → Set (lsuc α)
HProp α = HLevel α 1


HSet : ∀ α → Set (lsuc α)
HSet α = HLevel α 2


HLevel-suc : ∀ {α n} → HLevel α n → HLevel α (suc n)
HLevel-suc (HLevel⁺ A A-level) = HLevel⁺ A (IsOfHLevel-suc _ A-level)


⊤-IsContr : IsContr ⊤
⊤-IsContr = ⊤.tt , λ { ⊤.tt → refl }


⊤-IsProp : IsProp ⊤
⊤-IsProp = IsOfHLevel-suc 0 ⊤-IsContr


⊥-IsProp : IsProp ⊥
⊥-IsProp ()


×-IsProp : IsProp A → IsProp B → IsProp (A × B)
×-IsProp A-prop B-prop (x , y) (x′ , y′) = cong₂ _,_ (A-prop _ _) (B-prop _ _)


Lift-IsProp : IsProp A → IsProp (Lift α A)
Lift-IsProp A-prop (lift x) (lift y) = cong lift (A-prop _ _)


⊤-HProp : HProp 0ℓ
⊤-HProp = HLevel⁺ ⊤ ⊤-IsProp


⊥-HProp : HProp 0ℓ
⊥-HProp = HLevel⁺ ⊥ ⊥-IsProp


_×-HProp_ : HProp α → HProp β → HProp (α ⊔ℓ β)
A ×-HProp B = HLevel⁺ (A .type × B .type) (×-IsProp (A .level) (B .level))


Lift-HProp : ∀ α → HProp β → HProp (α ⊔ℓ β)
Lift-HProp α (HLevel⁺ A A-prop) = HLevel⁺ (Lift α A) (Lift-IsProp A-prop)


⊤-IsSet : IsSet ⊤
⊤-IsSet = IsOfHLevel-suc 1 ⊤-IsProp


⊥-IsSet : IsSet ⊥
⊥-IsSet = IsOfHLevel-suc 1 ⊥-IsProp


Σ-IsSet : {A : Set α} {B : A → Set β}
  → IsSet A
  → (∀ a → IsSet (B a))
  → IsSet (Σ A B)
Σ-IsSet A-set B-set p q
  = trans (sym (Σ-≡⁺∘Σ-≡⁻ p))
      (sym (trans (sym (Σ-≡⁺∘Σ-≡⁻ q))
      (cong Σ-≡⁺ (Σ-≡⁺ (A-set _ _ , B-set _ _ _)))))


×-IsSet : IsSet A → IsSet B → IsSet (A × B)
×-IsSet A-set B-set = Σ-IsSet A-set (λ _ → B-set)


Lift-IsSet : IsSet A → IsSet (Lift α A)
Lift-IsSet A-set p q
  = trans (sym (Lift-≡⁺∘Lift-≡⁻ p))
      (sym (trans (sym (Lift-≡⁺∘Lift-≡⁻ q)) (cong Lift-≡⁺ (A-set _ _))))
  where
    Lift-≡⁻ : {x y : Lift α A} → x ≡ y → lower x ≡ lower y
    Lift-≡⁻ refl = refl

    Lift-≡⁺ : {x y : Lift α A} → lower x ≡ lower y → x ≡ y
    Lift-≡⁺ refl = refl

    Lift-≡⁻∘Lift-≡⁺ : {x y : Lift α A} (p : lower x ≡ lower y)
      → Lift-≡⁻ {α = α} (Lift-≡⁺ p) ≡ p
    Lift-≡⁻∘Lift-≡⁺ refl = refl

    Lift-≡⁺∘Lift-≡⁻ : {x y : Lift α A} (p : x ≡ y)
      → Lift-≡⁺ {α = α} (Lift-≡⁻ p) ≡ p
    Lift-≡⁺∘Lift-≡⁻ refl = refl


⊤-HSet : HSet 0ℓ
⊤-HSet = HLevel⁺ ⊤ ⊤-IsSet


⊥-HSet : HSet 0ℓ
⊥-HSet = HLevel⁺ ⊥ ⊥-IsSet


Σ-HSet : (A : HSet α) (B : A .type → HSet β) → HSet (α ⊔ℓ β)
Σ-HSet A B
  = HLevel⁺ (Σ (A .type) λ a → B a .type) (Σ-IsSet (A .level) (λ a → B a .level))


_×-HSet_ : HSet α → HSet β → HSet (α ⊔ℓ β)
A ×-HSet B = HLevel⁺ (A .type × B .type) (×-IsSet (A .level) (B .level))


Lift-HSet : ∀ α → HSet β → HSet (α ⊔ℓ β)
Lift-HSet α (HLevel⁺ B B-set) = HLevel⁺ (Lift α B) (Lift-IsSet B-set)


IsProp∧Pointed→IsContr : IsProp A → (a : A) → IsContr A
IsProp∧Pointed→IsContr A-prop a = a , λ b → A-prop a b
