# Model

## Preliminaries

### Grothendieck

#### Definition

Let ℂ a category; F : ℂ → Cats. The Grothendieck category Σ ℂ F has

- objects: pairs (x₀, x₁) with x₀ ∈ ℂ; x₁ ∈ F x₁
- morphisms between (x₀, x₁) and (y₀,y₁): pairs (f₀,f₁) with
  * f₀ : x₀ → y₀
  * f₁ : F f₀ x₁ → y₁   [F f₀ : F x₀ → F y₀ ∈ Cats]
- identity: (id : x₀ → x₀, id : F id x₁ → x₁) : (x₀, x₁) → (x₀, x₁)
- composition: Let
  * (f₀, f₁) : (y₀, y₁) → (z₀, z₁)
  * (g₀, g₁) : (x₀, x₁) → (y₀, y₁)
  We have
  * g₀ : x₀ → y₀        ∈ ℂ
  * g₁ : F g₀ x₁ → y₁   ∈ F y₀
  * f₀ : y₀ → z₀        ∈ ℂ
  * f₁ : F f₀ y₁ → z₁   ∈ F z₀
  The composition is (h₀, h₁) with
  * h₀ : x₀ → z₀        ∈ ℂ
    h₀ ≔ f₀ ∘ g₀
  * h₁ : F h₀ x₁ → z₁   ∈ F z₀
       = F (f₀ ∘ g₀) x₁ → z₁
       = F f₀ (F g₀ x₁) → z₁
  * h₁ ≔ f₁              ∘ F f₀ g₁
         : F f₀ y₁ → z₁    : F f₀ (F g₀ x₁) → F f₀ y₁
- left identity: Let (f₀, f₁) : (x₀, x₁) → (y₀, y₁).
  (id, id) ∘ (f₀, f₁)
  = (id ∘ f₀, id ∘ F id f₁)
  = (f₀, f₁)
- right identity: similar.
- associativity:
  Let (f₀, f₁), (g₀, g₁), (h₀, h₁) compatible.
  * ((f₀, f₁) ∘ (g₀, g₁)) ∘ (h₀, h₁)
    = (f₀ ∘ g₀, f₁ ∘ F f₀ g₁) ∘ (h₀, h₁)
    = (f₀ ∘ g₀ ∘ h₀, f₁ ∘ F f₀ g₁ ∘ F (f₀ ∘ g₀) g₁)
  * (f₀, f₁) ∘ ((g₀, g₁) ∘ (h₀, h₁))
    = (f₀, f₁) ∘ (g₀ ∘ h₀, g₁ ∘ F g₀ h₁)
    = (f₀ ∘ g₀ ∘ h₀, f₁ ∘ F f₀ (g₁ ∘ F g₀ h₁))
    = (f₀ ∘ g₀ ∘ h₀, f₁ ∘ F f₀ g₁ ∘ F (f₀ ∘ g₀) h₁)

#### Projections

[Note: unusual naming.]

π₁ : Σ C F → C   ∈ Cats
π₁ (x₀, x₁) ≔ x₀
π₁ (f₀, f₁) : π₁ (x₀, x₁) → π₁ (y₀, y₁)
π₁ (f₀, f₁) ≔ f₀


π₀ : (x ∈ Σ C F) → F (π₁ x)
π₀ (x₀ , x₁) ≔ x₁

[Is there a notion of 'dependent functor'?]


### 𝕆≤

𝕆≤ : 𝕆 → Cats
𝕆≤ k ≔ {l : 𝕆 | l ≤ k}
𝕆≤ (f : n ≤ m) : 𝕆≤ n → 𝕆≤ m
𝕆≤ f k ≔ k                      [k ≤ n ≤ m]


### 𝕆<

similar


### ≲ : Rel 𝕆≤ω

n ≲ m ≔ m < ∞ → n < m


### 𝕆≲

𝕆≲ : 𝕆 → Cats
𝕆≲ k ≔ {l : 𝕆 | l ≲ k}
𝕆≲ (f : n ≤ m) : 𝕆≲ n → 𝕆≲ m
𝕆≲ f k ≔ k                      [k ≲ n ≤ m ; ≲ ⊂ ≤]


## Sizes

### ⟦Δ⟧

⟦Δ⟧ : Category

⟦[]⟧ ≔ ⊤
⟦Δ ∷ α≲n⟧ ≔ Σ ⟦Δ⟧ (𝕆≲ ∘ Incl ∘ ⟦Δ ⊢ n⟧)

[Incl is the inclusion from 𝕆≲ω to 𝕆.]


### ⟦Δ ⊢ i⟧

⟦Δ ⊢ i⟧ : ⟦Δ⟧ → 𝕆≲ω

⟦α⟧ ≔ Incl ∘ πα
⟦suc i⟧ ≔ (+ 1) ∘ ⟦i⟧

[πα is the α-th projection (counting from 0 and from the right). Incl is the
inclusion from 𝕆≲n into 𝕆≲ω.]


### ⟦Δ ⊢ n⟧

⟦Δ ⊢ n⟧ : ⟦Δ⟧ → 𝕆≤ω

⟦i⟧ ≔ ⟦i⟧                   [inclusion]
⟦∞⟧ ≔ Const ω

[Const is the constant functor.]


## Renamings

### ⟦Δ ⊇ Δ′⟧

⟦Δ ⊇ Δ′⟧ : Δ → Δ′

⟦[] : [] ⊇ []⟧ : ⊤ → ⊤

⟦weak : Δ ⊇ Δ′ → Δ ∷ n ⊇ Δ′⟧ : (⟦Δ⟧ → ⟦Δ′⟧) → (⟦Δ ∷ n⟧ → ⟦Δ′⟧)
⟦weak⟧ F ≔ F ∘ π₁

⟦lift : (θ : Δ ⊇ Δ′) → Δ ∷ m[θ] ⊇ Δ′ ∷ m⟧ : (⟦Δ⟧ → ⟦Δ′⟧) → (⟦Δ ∷ m[θ]⟧ → ⟦Δ′ ∷ m⟧)
⟦lift⟧ F ≔ ⟨ F × id ⟩

[⟨·×·⟩ should be the Grothendieck equivalent of bimap on Cartesian products]

wk : Δ ∷ n ⊇ Δ
wk ≔ weak idR
⟦wk⟧ = π₁


### ⟦n[θ]⟧

Assume θ : Δ ⊇ Δ′; Δ′ ⊢ n.

⟦Δ ⊢ n[θ]⟧ : ⟦Δ⟧ → 𝕆≲ω
⟦Δ ⊢ n[θ]⟧ ≔ ⟦Δ′ ⊢ n⟧ ∘ ⟦θ⟧


## Relations on Sizes


### ⟦Δ ⊢ Bound α i⟧

⟦Δ ⊢ Bound α i⟧ : ⟦Δ ⊢ α⟧ ≲ ⟦Δ ⊢ i⟧

⟦zero : Δ ∷ i ⊢ Bound 0 i[wk]⟧:
  ⟦Δ ∷ i⟧ = Σ ⟦Δ⟧ ⟦Δ ⊢ i⟧

  ⟦Δ ∷ i ⊢ 0⟧ (x , y)
    = (incl ∘ π₀) (x , y)
    = incl y
    ≲ ⟦Δ ⊢ i⟧ x                [y ∈ 𝕆≲(⟦Δ ⊢ i⟧ x)]
    = (⟦Δ ⊢ i⟧ ∘ π₁) (x , y)
    = ⟦Δ ∷ i ⊢ i[wk]⟧ (x , y)


⟦suc : Bound α i → Bound (α + 1) i[wk]⟧:
  TODO


### ⟦Δ ⊢ n ≲ m⟧

⟦Δ ⊢ n ≲ m⟧ : ⟦Δ ⊢ n⟧ ≲ ⟦Δ ⊢ m⟧

TODO


## Types

### ⟦Δ ⊢ T⟧

⟦Δ ⊢ T⟧ : ⟦Δ⟧ → Sets

⟦Δ ⊢ ℕ n⟧ ≔ ℕ< ∘ ⟦Δ ⊢ n⟧

⟦Δ ⊢ T ⇒ U⟧ ≔ ⟦Δ ⊢ T⟧ ⇒ ⟦Δ ⊢ U⟧     [F ⇒ G is the functor exponential.]

⟦Δ ⊢ ∀ α≲n. T⟧ : ⟦Δ⟧ → Sets
⟦Δ ⊢ ∀ α≲n. T⟧ δ ≔ { (m, T) | m ∈ 𝕆≲(⟦Δ ⊢ n⟧ δ), T ∈ ⟦Δ ∷ α≲n ⊢ T⟧ (δ , m) }
  where
    ⟦Δ ⊢ n⟧ : ⟦Δ⟧ → 𝕆≲ω
    ⟦Δ ∷ α≲n ⊢ T⟧ : ⟦Δ ∷ α≲n⟧ → Sets

⟦Δ ⊢ ∀ α≲n. T⟧ (f : δ ≤ δ′) : ⟦Δ ⊢ ∀ α ≲ n. T⟧ δ → ⟦Δ ⊢ ∀ α≲n. T⟧ δ′
⟦Δ ⊢ ∀ α≲n. T⟧ f (m , T) ≔ (m′, T′)
  where
    m′ ∈ 𝕆≲(⟦Δ ⊢ n⟧ δ′)
    m′ ≔ (𝕆≲ ∘ Incl ∘ ⟦Δ ⊢ n⟧) f m
    T′ ∈ ⟦Δ ∷ α≲n ⊢ T⟧ (δ′ , m′)
    T′ ≔ ⟦Δ ∷ α≲n ⊢ T⟧ g (m , T) ???
    g : (δ , m) ≤ (δ′, m′)


# Graveyard


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

⟦≤→<S : i ≤ j → i < suc j⟧:
  ⟦i ≤ j⟧ : ⟦i⟧ ≤ ⟦j⟧

  ⟦i < suc j⟧ : ⟦i⟧ < (+ 1) ∘ ⟦j⟧


⟦suc-cong : i < j → suc i < suc j⟧:
  ⟦i < j⟧ : ⟦i⟧ < ⟦j⟧

  ⟦suc i < suc j⟧ : (+ 1) ∘ ⟦i⟧ < (+ 1) ∘ ⟦j⟧


### ⟦Δ ⊢ n ≤∞ m⟧

⟦Δ ⊢ n ≤∞ m⟧ : ∀ δ ∈ ⟦Δ⟧. ⟦Δ ⊢ n⟧ δ ≤ ⟦Δ ⊢ m⟧ δ

⟦si : i ≤ j → i ≤∞ j⟧: trivial

⟦∞ : n ≤‌∞ ∞⟧: ⟦Δ ⊢ n⟧ δ ∈ 𝕆≤ω


### ⟦Δ ⊢ n <∞ m⟧

⟦Δ ⊢ n <∞ m⟧ : ∀ δ ∈ ⟦Δ⟧. ⟦Δ ⊢ n⟧ δ < ⟦Δ ⊢ m⟧ δ

⟦si : i < j → i <∞ j⟧: trivial

⟦∞ : i < ∞⟧: ⟦Δ ⊢ i⟧ δ ∈ 𝕆<ω
