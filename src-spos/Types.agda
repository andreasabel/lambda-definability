module Types where

open import Library

-- Strictly positive types

TyVar = Fin

data _≥_ : (n m : ℕ) → Set where
  id≥  : ∀{n} → n ≥ n
  weak : ∀{n m} (n≤m : n ≥ m) → suc n ≥ m
  lift : ∀{n m} (n≤m : n ≥ m) → suc n ≥ suc m

wkTyVar : ∀ {n m} → TyVar m → n ≥ m → TyVar n
wkTyVar X       id≥ = X
wkTyVar X       (weak n≥m) = Fin.suc (wkTyVar X n≥m)
wkTyVar zero    (lift n≥m) = zero
wkTyVar (suc X) (lift n≥m) = suc (wkTyVar X n≥m)

data Ty (n : ℕ) : Set where
  Var : (X : TyVar n) → Ty n
  0̂ 1̂ : Ty n
  _+̂_ _×̂_ : (a b : Ty n) → Ty n
  _→̂_ : (a : Ty 0) (b : Ty n) → Ty n
  μ̂ ν̂ : (f : Ty (suc n)) → Ty n

wkTy : ∀{n m} (a : Ty m) (n≥m : n ≥ m) → Ty n
wkTy (Var X) n≥m = Var (wkTyVar X n≥m)
wkTy 0̂       n≥m = 0̂
wkTy 1̂       n≥m = 1̂
wkTy (a +̂ b) n≥m = wkTy a n≥m +̂ wkTy b n≥m
wkTy (a ×̂ b) n≥m = wkTy a n≥m ×̂ wkTy b n≥m
wkTy (a →̂ b) n≥m = a →̂ wkTy b n≥m
wkTy (μ̂ f) n≥m = μ̂ (wkTy f (lift n≥m))
wkTy (ν̂ f) n≥m = ν̂ (wkTy f (lift n≥m))

-- Type interpretation

⦅_⦆ : ∀{n} (a : Ty n) {ℓ} (ρ : Vec (Set ℓ) n) → Set ℓ
⦅ Var X ⦆ ρ = lookup X ρ
⦅ 0̂ ⦆ ρ = Lift ⊥
⦅ 1̂ ⦆ ρ = Lift ⊤
⦅ a +̂ b ⦆ ρ = ⦅ a ⦆ ρ ⊎ ⦅ b ⦆ ρ
⦅ a ×̂ b ⦆ ρ = ⦅ a ⦆ ρ × ⦅ b ⦆ ρ
⦅ a →̂ b ⦆ {ℓ} ρ = ⦅ a ⦆ {ℓ} [] → ⦅ b ⦆ ρ
⦅ μ̂ f ⦆ ρ = {! Mu α λ X → ⦅ f ⦆ (X ∷ ρ) !}
⦅ ν̂ f ⦆ ρ = {! Nu α λ X → ⦅ f ⦆ (X ∷ ρ) !}

-- Functoriality

data Arr {ℓ} : ∀ {n} (ρ₁ ρ₂ : Vec (Set ℓ) n) → Set ℓ where
  [] : Arr [] []
  _∷_ : ∀{n} {A B : Set ℓ} {ρ₁ ρ₂ : Vec _ n} (f : A → B) (fs : Arr {ℓ} ρ₁ ρ₂) → Arr (A ∷ ρ₁) (B ∷ ρ₂)

lookupArr : ∀ {n} {ρ ρ′ : Vec Set n} (X : Fin n) → Arr ρ ρ′ → lookup X ρ → lookup X ρ′
lookupArr zero    (f ∷ fs) = f
lookupArr (suc X) (f ∷ fs) = lookupArr X fs

map : ∀{n} (a : Ty n) {ρ ρ′} (fs : Arr ρ ρ′) → ⦅ a ⦆ ρ → ⦅ a ⦆ ρ′
map (Var X) fs = lookupArr X fs
map 0̂       fs ()
map 1̂       fs = _
map (a +̂ b) fs = map a fs +̇ map b fs
map (a ×̂ b) fs = map a fs ×̇ map b fs
map (a →̂ b) fs g = map b fs ∘′ g
map (μ̂ F) fs = {! mapMu (λ g → map F (g ∷ fs)) α !}
map (ν̂ F) fs = {! mapNu (λ g → map F (g ∷ fs)) α !}
