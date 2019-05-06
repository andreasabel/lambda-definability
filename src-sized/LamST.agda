module LamST where

open import Relation.Binary using
  (Reflexive ; Sym ; Symmetric ; Trans ; Transitive)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl)


infix  0 _≈SS_
infixl 1 _∷_ _∷[_]_
infixr 2 Π_,_
infixr 3 _⇒_
infixr 5 _∙_


mutual
  -- Size contexts are iterated dependent sums of size bounds.
  data SC : Set where
    [] : SC
    _∷_ : (Δ : SC) (i : Si Δ) → SC


  -- Size variables are indexes into a size context.
  data SV : (Δ : SC) → Set where
    zero : ∀ {Δ i} → SV (Δ ∷ i)
    suc : ∀ {Δ i} (α : SV Δ) → SV (Δ ∷ i)


  -- Sizes with variables in a given context.
  data Si Δ : Set where
    var : (α : SV Δ) → Si Δ
    suc : (i : Si Δ) → Si Δ
    ∞ : Si Δ


variable
  Δ Δ′ Δ″ : SC
  i j k : Si Δ
  α β : SV Δ


wkSV : SV Δ → SV (Δ ∷ i)
wkSV zero = suc zero
wkSV (suc α) = suc (wkSV α)


wkSi : Si Δ → Si (Δ ∷ i)
wkSi (var α) = var (wkSV α)
wkSi (suc i) = suc (wkSi i)
wkSi ∞ = ∞


bound : (α : SV Δ) → Si Δ
bound (zero {i = i}) = wkSi i
bound (suc α) = wkSi (bound α)


bound-wkSV : (α : SV Δ) → bound (wkSV {i = i} α) ≡ wkSi (bound α)
bound-wkSV zero = refl
bound-wkSV (suc α) = ≡.cong wkSi (bound-wkSV α)


module _ {Δ : SC} where
  -- TODO better naming in this module
  -- redundancy in the definitions of < and ≤?

  infix 0  _<_ _≤_


  mutual
    -- A preorder on sizes.
    data _≤_ : (i j : Si Δ) → Set where
      refl : i ≤ i
      <→≤ : i < j → i ≤ j


    -- A strict order on sizes.
    data _<_ : (i j : Si Δ) → Set where
      var
        : bound α ≤ i
        → var α < i
      suc
        : i ≤ j
        → i < suc j
      suc-cong
        : i < j
        → suc i < suc j
      ∞
        : i < ∞ -- ???


  <-suc′ : i < suc i
  <-suc′ = suc refl


  mutual
    ≤-suc″ : suc j ≤ k → j ≤ k
    ≤-suc″ refl = <→≤ <-suc′
    ≤-suc″ (<→≤ x) = <→≤ (<-suc″ x)


    <-suc″ : suc j < k → j < k
    <-suc″ (suc Sj≤k) = suc (≤-suc″ Sj≤k)
    <-suc″ (suc-cong j<k) = suc (<→≤ j<k)
    <-suc″ ∞ = ∞


  <-suc‴ : suc j ≤ k → j < k
  <-suc‴ refl = <-suc′
  <-suc‴ (<→≤ Sj<k) = <-suc″ Sj<k


  mutual
    ∞<i-elim : ∞ < i → j < i
    ∞<i-elim (suc ∞≤j) = <-trans <-suc′ (suc-cong (∞≤i-elim ∞≤j))
    ∞<i-elim ∞ = ∞


    ∞≤i-elim : ∞ ≤ i → j < i
    ∞≤i-elim refl = ∞
    ∞≤i-elim (<→≤ x) = ∞<i-elim x


    ≤→<→< : i ≤ j → j < k → i < k
    ≤→<→< refl j<k = j<k
    ≤→<→< (<→≤ i<j) j<k = <-trans i<j j<k


    <→≤→< : i < j → j ≤ k → i < k
    <→≤→< i<j refl = i<j
    <→≤→< i<j (<→≤ j<k) = <-trans i<j j<k


    <-trans : i < j → j < k → i < k
    <-trans (var bα≤j) j<k = var (<→≤ (≤→<→< bα≤j j<k))
    <-trans (suc i≤j) j<k = ≤→<→< i≤j (<-suc″ j<k)
    <-trans (suc-cong i<j) (suc x) = suc-cong (<-trans i<j (<-suc‴ x))
    <-trans (suc-cong i<j) (suc-cong j<k) = suc-cong (<-trans i<j j<k)
    <-trans (suc-cong i<j) ∞ = ∞
    <-trans ∞ (suc i<Sj) = suc (<→≤ (∞≤i-elim i<Sj))
    <-trans ∞ ∞ = ∞


  bound-resp-< : var α < var β → bound α < bound β
  bound-resp-< {α} {β} (var bα≤β) = ≤→<→< bα≤β (var refl)


  ≤-trans : i ≤ j → j ≤ k → i ≤ k
  ≤-trans refl j≤k = j≤k
  ≤-trans (<→≤ i<j) j≤k = <→≤ (<→≤→< i<j j≤k)


  suc-resp-≤ : i ≤ j → suc i ≤ suc j
  suc-resp-≤ refl = refl
  suc-resp-≤ (<→≤ i<j) = <→≤ (suc-cong i<j)


  <→≤→≤ : i < j → j ≤ k → i ≤ k
  <→≤→≤ i<j j≤k = <→≤ (<→≤→< i<j j≤k)


  ≤→<→≤ : i ≤ j → j < k → i ≤ k
  ≤→<→≤ i≤j j<k = <→≤ (≤→<→< i≤j j<k)


mutual
  wkSi-resp-≤ : i ≤ j → wkSi {i = k} i ≤ wkSi j
  wkSi-resp-≤ refl = refl
  wkSi-resp-≤ (<→≤ i<j) = <→≤ (wkSi-resp-< i<j)


  wkSi-resp-< : i < j → wkSi {i = k} i < wkSi j
  wkSi-resp-< (var {zero} bα≤j) = var (wkSi-resp-≤ bα≤j)
  wkSi-resp-< (var {suc {i = i} α} bα≤j)
    rewrite ≡.sym (bound-wkSV {i = i} α)
    = var (wkSi-resp-≤ bα≤j)
  wkSi-resp-< (suc i≤j) = suc (wkSi-resp-≤ i≤j)
  wkSi-resp-< (suc-cong i<j) = suc-cong (wkSi-resp-< i<j)
  wkSi-resp-< ∞ = ∞


mutual
  -- Size substitutions. SS Δ Δ′ is a morphism from Δ to Δ′, viewing both as
  -- product categories.
  data SS : (Δ Δ′ : SC) → Set where
    [] : SS Δ []
    _∷[_]_
      : (σ : SS Δ Δ′)
      → ∀ i {j} (i<j : i < j)
      → SS Δ (Δ′ ∷ j)
    wk : SS (Δ ∷ i) Δ
    id : SS Δ Δ
    _∙_
      : (σ : SS Δ′ Δ″)
      → (δ : SS Δ Δ′)
      → SS Δ Δ″


-- Equality on size substitutions.
data _≈SS_ : (σ δ : SS Δ Δ′) → Set where
  id-l : {σ : SS Δ Δ′}
    → id ∙ σ ≈SS σ
  id-r : {σ : SS Δ Δ′}
    → σ ∙ id ≈SS σ
  _∙_ : {σ σ′ : SS Δ′ Δ″} {δ δ′ : SS Δ Δ′}
    → σ ≈SS σ′
    → δ ≈SS δ′
    → σ ∙ δ ≈SS σ′ ∙ δ′
  _∷_ : ∀ {σ δ : SS Δ Δ′} {i j} {i<j : i < j}
    → σ ≈SS δ
    → σ ∷[ i ] i<j ≈SS δ ∷[ i ] i<j
  refl : Reflexive (_≈SS_ {Δ} {Δ′})
  sym : Symmetric (_≈SS_ {Δ} {Δ′})
  trans : Transitive (_≈SS_ {Δ} {Δ′})


mutual
  subSV : (σ : SS Δ′ Δ) (α : SV Δ) → Si Δ′
  subSV (σ ∷[ i ] i<j) zero = subSi σ i
  subSV (σ ∷[ i ] i<j) (suc α) = subSV σ α
  subSV wk α = var (wkSV α)
  subSV id α = var α
  subSV (σ ∙ δ) α = subSi δ (subSV σ α)


  subSi : (σ : SS Δ′ Δ) (i : Si Δ) → Si Δ′
  subSi σ (var α) = subSV σ α
  subSi σ (suc i) = suc (subSi σ i)
  subSi σ ∞ = ∞


subSi-id : subSi id i ≡ i
subSi-id {i = var α} = refl
subSi-id {i = suc i} = ≡.cong suc subSi-id
subSi-id {i = ∞} = refl


subSi-∙ : {σ : SS Δ′ Δ″} {δ : SS Δ Δ′}
  → subSi (σ ∙ δ) i ≡ subSi δ (subSi σ i)
subSi-∙ = {!!}


subSi-wk : subSi wk j ≡ wkSi {i = i} j
subSi-wk {j = var α} = refl
subSi-wk {j = suc j} = ≡.cong suc subSi-wk
subSi-wk {j = ∞} = refl


subSi-[] : subSi [] i ≡ i
subSi-[] {suc i} = ≡.cong suc subSi-[]
subSi-[] {∞} = refl


mutual
  subSi-resp-≤ : ∀ (σ : SS Δ′ Δ) {i j} → i ≤ j → subSi σ i ≤ subSi σ j
  subSi-resp-≤ σ refl = refl
  subSi-resp-≤ σ (<→≤ i<j) = <→≤ (subSi-resp-< σ i<j)


  subSi-resp-< :  ∀ (σ : SS Δ′ Δ) {i j} → i < j → subSi σ i < subSi σ j
  subSi-resp-< σ (var bα≤j) = subSV-resp-< σ bα≤j
  subSi-resp-< σ (suc i≤j) = suc (subSi-resp-≤ σ i≤j)
  subSi-resp-< σ (suc-cong i<j) = suc-cong (subSi-resp-< σ i<j)
  subSi-resp-< σ ∞ = ∞


  subSV-resp-< : ∀ (σ : SS Δ′ Δ) {α : SV Δ} {i} → bound α ≤ i → subSV σ α < subSi σ i
  subSV-resp-< (σ ∷[ k ] k<j) {zero} {var zero} α<i = {!α<i!}
  subSV-resp-< (σ ∷[ k ] k<j) {zero} {var (suc α)} α<i = {!!}
  subSV-resp-< (σ ∷[ k ] k<j) {zero} {suc i} α<i = suc {!!}
  subSV-resp-< (σ ∷[ k ] k<j) {zero} {∞} α<i = ∞
  subSV-resp-< (σ ∷[ k ] k<j) {suc α} {i} α<i = {!!}
  subSV-resp-< wk {α} {i} α<i = {!!}
  subSV-resp-< id {α} {i} α<i = {!!}
  subSV-resp-< (σ ∙ σ₁) {α} {i} α<i = {!!}


-- Types.
data Ty Δ : Set where
  ℕ : (i : Si Δ) → Ty Δ
  _⇒_ : (T U : Ty Δ) → Ty Δ
  Π_,_ : (i : Si Δ) (T : Ty (Δ ∷ i)) → Ty Δ


skip : (σ : SS Δ Δ′) → SS (Δ ∷ subSi σ i) (Δ′ ∷ i)
skip {i = i} [] = {!!}
skip (σ ∷[ i ] i<j) = {!!}
skip wk = {!!}
skip {i = i} id rewrite subSi-id {i = i} = id
skip {i = i} (σ ∙ δ) rewrite subSi-∙ {i = i} {σ} {δ} = {!? ∙ skip σ!}


_∷SS_ : (σ : SS Δ Δ′) → i ≤ subSi σ j → SS (Δ ∷ i) (Δ′ ∷ j)
σ ∷SS refl = {!!}
σ ∷SS <→≤ x = {!!}


subTy : (σ : SS Δ′ Δ) (T : Ty Δ) → Ty Δ′
subTy σ (ℕ i) = ℕ (subSi σ i)
subTy σ (T ⇒ U) = subTy σ T ⇒ subTy σ U
subTy σ (Π i , T) = Π subSi σ i , {!!}


{-
-- _∷SS_ : ∀ {Δ Δ′ i j} → SS Δ Δ′ → i ≤ j → SS (Δ ∷ i) (Δ′ ∷ j)
-- σ ∷SS refl = id
-- _∷SS_ {i = i} {j} σ (<→≤ i<j) = {!_∷_ ? {i = i [ σ ]} ?!} -- _∷_ {i = i} (σ ∙ wk) {!!}
-- σ ∷SS cong x x₁ i≤j = {!!}


-- Type contexts.
data TC Δ : Set where
  [] : TC Δ
  _∷_ : (Γ : TC Δ) (T : Ty Δ) → TC Δ


variable
  Γ : TC Δ

data Tm : (Δ : SC) (Γ : TC Δ) (T : Ty Δ) → Set where
  v0 : ∀ {Δ} {Γ : TC Δ} {T : Ty Δ}
    → Tm Δ (Γ ∷ T) T
  wk : ∀ {Δ} {Γ : TC Δ} {T : Ty Δ}
    → (t : Tm Δ Γ T)
    → {U : Ty Δ}
    → Tm Δ (Γ ∷ U) T
  Λ_,_ : ∀ {Δ} {Γ : TC Δ}
    → (T : Ty Δ)
    → {U : Ty Δ} (t : Tm Δ (Γ ∷ T) U)
    → Tm Δ Γ (T ⇒ U)
  _·_ : ∀ {Δ} {Γ : TC Δ} {T U : Ty Δ}
    → (t : Tm Δ Γ (T ⇒ U))
    → (u : Tm Δ Γ T)
    → Tm Δ Γ U
  Λₛ_,_ : ∀ {Δ} {Γ : TC Δ}
    → (i : Si Δ)
    → {T : Ty (Δ ∷ i)} (t : Tm (Δ ∷ i) (Γ [ wk ]) T)
    → Tm Δ Γ (Π i , T)
  _·ₛ_ : ∀ {Δ} {Γ : TC Δ} {i : Si Δ} {T : Ty (Δ ∷ i)}
    → (t : Tm Δ Γ (Π i , T))
    → {j : Si Δ}
    → (j<i : j < i)
    → Tm Δ Γ (T [ id ∷ j<i ])
  zero : ∀ {Δ} {Γ : TC Δ} {i : Si Δ}
    → Tm Δ Γ (ℕ i)
  suc : ∀ {Δ} {Γ : TC Δ}
    → Tm Δ Γ (Π ∞ , Π (v0 _) , ℕ (v0 _) ⇒ ℕ (v0 _ [ wk ]))
  caseℕ[_] : ∀ {Δ} {Γ : TC Δ} (T : Ty Δ)
    → Tm Δ Γ (Π ∞ , T [ wk ] ⇒ (Π (v0 _) , ℕ (v0 _) ⇒ T [ wk ∙ wk ]) ⇒ ℕ (v0 _) ⇒ T [ wk ])
  fix[_] : ∀ {Δ} {Γ : TC Δ} (T : Ty (Δ ∷ ∞))
    → Tm Δ Γ ((Π ∞ , (Π (v0 _) , T [ wk ]) ⇒ T) ⇒ (Π ∞ , T))
  cast : ∀ {Δ Δ′} {Γ : TC Δ} {Γ′ : TC Δ′} {T : Ty Δ} {U : Ty Δ′}
    → Γ ≈TC Γ′
    → T ≈Ty U
    → Tm Δ Γ T
    → Tm Δ′ Γ′ U


-- one : ∀ {Δ Γ} → Tm Δ Γ (ℕ ∞)
-- one = cast {!!} {!!} ((cast {!refl!} {!sub-∷!} (suc ·ₛ ∞)) ·ₛ {!!}) · {!!}
-}
