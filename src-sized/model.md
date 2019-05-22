# Model

## Preliminaries

### 𝕆<

𝕆< : 𝕆 → Cat
𝕆< k ≔ {l : 𝕆 | l < k}
𝕆< (f : n ≤ m) : 𝕆< n → 𝕆< m
𝕆< f k ≔ k                      [k < n ≤ m]


## Sizes

### ⟦Δ⟧

⟦Δ⟧ : Category

⟦[]⟧ ≔ ⊤
⟦Δ ∷ α<n⟧ ≔ Σ ⟦Δ⟧ (𝕆< ∘ ⟦Δ ⊢ n⟧)   [Σ C F is the Grothendieck category of a category C and functor F]


### ⟦Δ ⊢ i⟧

⟦Δ ⊢ i⟧ : ⟦Δ⟧ → 𝕆<ω

⟦α⟧ ≔ incl ∘ πα             [πα is the α-th projection (counting from 0). incl is the inclusion from 𝕆<n into 𝕆<ω.]
⟦suc i⟧ ≔ (+ 1) ∘ ⟦i⟧


### ⟦Δ ⊢ n⟧

⟦Δ ⊢ n⟧ : ⟦Δ⟧ → 𝕆≤ω

⟦i⟧ ≔ ⟦i⟧                   [inclusion]
⟦∞⟧ ≔ Const ω               [Const is the constant functor]


## Renamings

### ⟦Δ ⊇ Δ′⟧

⟦Δ ⊇ Δ′⟧ : Δ → Δ′

⟦[] : [] ⊇ []⟧ : ⊤ → ⊤

⟦weak : Δ ⊇ Δ′ → Δ ∷ n ⊇ Δ′⟧ : (⟦Δ⟧ → ⟦Δ′⟧) → (⟦Δ ∷ n⟧ → ⟦Δ′⟧)
⟦weak⟧ F ≔ F ∘ π₁

⟦lift : (θ : Δ ⊇ Δ′) → Δ ∷ m[θ] ⊇ Δ′ ∷ m⟧ : (⟦Δ⟧ → ⟦Δ′⟧) → (⟦Δ ∷ m[θ]⟧ → ⟦Δ′ ∷ m⟧)
⟦lift⟧ F ≔ ⟨ F × id ⟩    [⟨·×·⟩ should be the Grothendieck equivalent of bimap on Cartesian products]

wk : Δ ∷ n ⊇ Δ
wk ≔ weak idR
⟦wk⟧ = π₁


### ⟦n[θ]⟧

Let θ : Δ ⊇ Δ′; Δ′ ⊢ n.

⟦Δ ⊢ n[θ]⟧ : ⟦Δ⟧ → 𝕆≤ω
⟦Δ ⊢ n[θ]⟧ ≔ ⟦Δ′ ⊢ n⟧ ∘ ⟦θ⟧


## Relations on Sizes


### ⟦Δ ⊢ Bound α i⟧

⟦Δ ⊢ Bound α i⟧ : ∀ δ ∈ ⟦Δ⟧. ⟦Δ ⊢ α⟧ δ < ⟦Δ ⊢ i⟧ δ

⟦zero : Δ ∷ i ⊢ Bound 0 i[wk]⟧:
  ⟦Δ ∷ i⟧ = Σ ⟦Δ⟧ ⟦Δ ⊢ i⟧

  ⟦Δ ∷ i ⊢ 0⟧ (x , y)
    = (incl ∘ π₀) (x , y)
    = incl y
    < ⟦Δ ⊢ i⟧ x                [y ∈ 𝕆<(⟦Δ ⊢ i⟧ x)]
    = (⟦Δ ⊢ i⟧ ∘ π₁) (x , y)
    = ⟦Δ ∷ i ⊢ i[wk]⟧ (x , y)


⟦suc : Bound α i → Bound (α + 1) i[wk]⟧:
  TODO


### ⟦Δ ⊢ i ≤ j⟧

⟦Δ ⊢ i ≤ j⟧ : ∀ δ ∈ ⟦Δ⟧. ⟦Δ ⊢ i⟧ δ ≤ ⟦Δ ⊢ j⟧ δ

⟦refl : i ≤ i⟧: trivial
⟦<→≤ : i < j → i ≤ j⟧: trival


### ⟦Δ ⊢ i < j⟧

⟦Δ ⊢ i < j⟧ : ∀ δ ∈ ⟦Δ⟧. ⟦Δ ⊢ i⟧ δ < ⟦Δ ⊢ j⟧ δ

⟦var : Bound α i → i ≤ j → α < j⟧:
  ⟦Δ ⊢ Bound α i⟧ : ⟦Δ ⊢ α⟧ < ⟦Δ ⊢ i⟧

  ⟦Δ ⊢ i ≤ j⟧ : ⟦Δ ⊢ i⟧ ≤ ⟦Δ ⊢ j⟧

  ⟦Δ ⊢ α < j⟧ : ⟦Δ ⊢ α⟧ < ⟦Δ ⊢ j⟧
