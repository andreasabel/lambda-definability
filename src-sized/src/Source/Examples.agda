module Source.Examples where

open import Source.Size
open import Source.Term
open import Source.Type
open import Util.Prelude


{-
half : (n < ⋆) → Nat n → Nat n
half ≔ λ (n < ⋆). fix (λ (m < ⋆). Nat m → Nat m)
  (λ (n < ⋆) (rec : (m < n) → Nat m → Nat m).
    λ (i : Nat n). caseNat (Nat n) n i
      (zero n)
      (λ (m < n) (i′ : Nat m). caseNat (Nat n) m i′
        (zero n)
        (λ (k < m) (i″ : Nat k). rec k i″))
  n
-}
half : Term []
half = Λₛ ⋆ , fix (Nat v0 ⇒ Nat v0)
  (Λₛ ⋆ , Λ (Π v0 , Nat v0 ⇒ Nat v0) ,
    Λ Nat v0 , caseNat (Nat v0) v0 (var 0)
      (zero v0)
      (Λₛ v0 , Λ (Nat v0) , caseNat (Nat v1) v0 (var 0)
        (zero v1)
        (Λₛ v0 , Λ (Nat v0) , var 2 ·ₛ v0 · var 0)))
  v0


half⊢ : [] , [] ⊢ half ∶ Π ⋆ , Nat v0 ⇒ Nat v0
half⊢ = absₛ _ _ _
  (fix (var _ refl ≤-refl)
    (absₛ _ _ _
      (abs _ _
        (abs _ _
          (caseNat (var _ refl ≤-refl)
            (var 0 zero)
            (zero (var _ refl ≤-refl))
            (absₛ _ _ _
              (abs _ _
                (caseNat (var _ refl (<→≤ (var _ refl ≤-refl)))
                  (var 0 zero)
                  (zero (var _ refl ≤-refl))
                  (absₛ _ _ _
                    (abs _ _
                      {!!})
                    refl)
                  refl))
                refl)
            refl)))
      refl)
    refl
    refl)
  refl
