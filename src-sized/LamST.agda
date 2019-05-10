module LamST where

open import Relation.Binary using
  (Reflexive ; Sym ; Symmetric ; Trans ; Transitive)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl; module ≡-Reasoning)


infix  0 _⊇_ -- _≈SS_
infixl 1 _∷_ _∷[_]_
-- infixr 2 Π_,_
-- infixr 3 _⇒_
infixr 5 _∙_


mutual
  -- Size contexts are iterated dependent sums of size bounds.
  data SC : Set where
    [] : SC
    _∷_ : (Δ : SC) (i : Si Δ) → SC


  -- Size variables are indexes into a size context with a given bound.
  data SV : (Δ : SC) → Set where
    zero : ∀ {Δ i} → SV (Δ ∷ i)
    suc : ∀ {Δ i} (α : SV Δ) → SV (Δ ∷ i)


  -- Sizes with variables in a given context.
  data Si Δ : Set where
    var : (α : SV Δ) → Si Δ
    suc : (i : Si Δ) → Si Δ
    ∞ : Si Δ


variable
  Δ Δ′ Δ″ Ω : SC
  i j k : Si Δ
  α β : SV Δ


mutual
  -- Renamings.
  data _⊇_ : (Δ Δ′ : SC) → Set where
    []   : [] ⊇ []
    weak : (θ : Δ ⊇ Δ′) → Δ ∷ i ⊇ Δ′
    lift : (θ : Δ ⊇ Δ′) (p : renSi θ j ≡ i) → Δ ∷ i ⊇ Δ′ ∷ j


  renSi : (θ : Δ ⊇ Δ′) → Si Δ′ → Si Δ
  renSi θ (var α) = var (renSV θ α)
  renSi θ (suc i) = suc (renSi θ i)
  renSi θ ∞       = ∞


  renSV : Δ ⊇ Δ′ → SV Δ′ → SV Δ
  renSV (weak θ)  α       = suc (renSV θ α)
  renSV (lift θ p) zero    = zero
  renSV (lift θ p) (suc α) = suc (renSV θ α)


variable
  θ ι : Δ′ ⊇ Δ


cong-lift : ∀ {p q} → θ ≡ ι → lift {j = j} {i} θ p ≡ lift ι q
cong-lift {p = refl} {refl} refl = refl


mutual
  idR : Δ ⊇ Δ
  idR {[]}    = []
  idR {Δ ∷ i} = lift idR renSi-id

  renSi-id : {i : Si Δ} → renSi idR i ≡ i
  renSi-id {i = var α} = ≡.cong var renSV-id
  renSi-id {i = suc i} = ≡.cong suc renSi-id
  renSi-id {i = ∞}     = refl

  renSV-id : {α : SV Δ} → renSV idR α ≡ α
  renSV-id {α = zero}  = refl
  renSV-id {α = suc α} = ≡.cong suc renSV-id

mutual
  _∙_ : Δ ⊇ Δ′ → Δ′ ⊇ Δ″ →  Δ ⊇ Δ″
  [] ∙ ι = ι
  weak θ ∙ ι = weak (θ ∙ ι)
  lift θ p ∙ weak ι = weak (θ ∙ ι)
  lift θ p ∙ lift ι q
    = lift (θ ∙ ι) (≡.trans (≡.trans renSi-∙ (≡.cong (renSi θ) q)) p)

  renSi-∙ : renSi (θ ∙ ι) i ≡ renSi θ (renSi ι i)
  renSi-∙ {i = var α} = ≡.cong var renSV-∙
  renSi-∙ {i = suc i} = ≡.cong suc renSi-∙
  renSi-∙ {i = ∞} = refl

  renSV-∙ : renSV (θ ∙ ι) α ≡ renSV θ (renSV ι α)
  renSV-∙ {θ = []} {ι = []} {()}
  renSV-∙ {θ = weak θ} = ≡.cong suc renSV-∙
  renSV-∙ {θ = lift θ refl} {ι = weak ι} = ≡.cong suc renSV-∙
  renSV-∙ {θ = lift θ refl} {ι = lift ι refl} {zero} = refl
  renSV-∙ {θ = lift θ refl} {ι = lift ι refl} {suc α} = ≡.cong suc renSV-∙


∙-id-l : idR ∙ θ ≡ θ
∙-id-l {θ = []} = refl
∙-id-l {θ = weak θ} = ≡.cong weak ∙-id-l
∙-id-l {θ = lift θ p} = cong-lift ∙-id-l


∙-id-r : θ ∙ idR ≡ θ
∙-id-r {θ = []} = refl
∙-id-r {θ = weak θ} = ≡.cong weak ∙-id-r
∙-id-r {θ = lift θ p} = cong-lift ∙-id-r


weak′ : Δ ∷ i ⊇ Δ
weak′ = weak idR


lift∙weak′ : {θ : Δ ⊇ Δ′} {p : renSi θ i ≡ j} → lift θ p ∙ weak′ ≡ weak θ
lift∙weak′ = ≡.cong weak ∙-id-r


weak′∙ : {θ : Δ ⊇ Δ′} → weak′ {i = i} ∙ θ ≡ weak θ
weak′∙ = ≡.cong weak ∙-id-l


wkSV : SV Δ → SV (Δ ∷ i)
wkSV = renSV weak′


wkSi : Si Δ → Si (Δ ∷ i)
wkSi = renSi weak′


bound : (α : SV Δ) → Si Δ
bound (zero {i = i}) = wkSi i
bound (suc α) = wkSi (bound α)


bound-wkSV : (α : SV Δ) → bound (wkSV {i = i} α) ≡ wkSi (bound α)
bound-wkSV zero = refl
bound-wkSV (suc α) = ≡.cong wkSi (bound-wkSV α)


renSi-bound : renSi θ (bound α) ≡ bound (renSV θ α)
renSi-bound {θ = weak θ} {α} =
  let open ≡-Reasoning in
  begin
    renSi (weak θ) (bound α)
  ≡⟨ ≡.cong (λ z → renSi z (bound α)) (≡.sym weak′∙) ⟩
    renSi (weak idR ∙ θ) (bound α)
  ≡⟨ renSi-∙ ⟩
    wkSi (renSi θ (bound α))
  ≡⟨ ≡.cong wkSi renSi-bound ⟩
    wkSi (bound (renSV θ α))
  ∎
renSi-bound {θ = lift {j = j} {i} θ refl} {α} =
  let open ≡-Reasoning in
  {!!}
  -- begin
  --   renSi (lift θ refl) (renSi (weak idR) j)
  -- ≡⟨ ≡.sym renSi-∙ ⟩
  --   renSi (lift θ refl ∙ weak idR) j
  -- ≡⟨ ≡.cong (λ z → renSi (weak z) j) (≡.trans ∙-id-r (≡.sym ∙-id-l)) ⟩
  --   renSi (weak idR ∙ θ) j
  -- ≡⟨ renSi-∙ ⟩
  --   renSi (weak idR) (renSi θ j)
  -- ∎

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
  renSi-resp-≤ : (θ : Δ′ ⊇ Δ) → i ≤ j → renSi θ i ≤ renSi θ j
  renSi-resp-≤ θ refl = refl
  renSi-resp-≤ θ (<→≤ i<j) = <→≤ (renSi-resp-< θ i<j)

  renSi-resp-< : (θ : Δ′ ⊇ Δ) → i < j → renSi θ i < renSi θ j
  renSi-resp-< θ (var {zero} x) = var {!ren-< θ x!}
  renSi-resp-< θ (var {suc α} x) = var {!!}
  renSi-resp-< θ (suc i≤j) = suc (renSi-resp-≤ θ i≤j)
  renSi-resp-< θ (suc-cong i<j) = suc-cong (renSi-resp-< θ i<j)
  renSi-resp-< θ ∞ = ∞


mutual
  -- Size substitutions. SS Δ Δ′ is a morphism from Δ to Δ′, viewing both as
  -- product categories.
  data SS : (Δ Δ′ : SC) → Set where
    [] : SS Δ []
    _∷[_]_
      : (σ : SS Δ Δ′)
      → (i : Si Δ) {j : Si Δ′} (i<j : i < subSi σ j)
      → SS Δ (Δ′ ∷ j)


  subSV : (σ : SS Δ′ Δ) (α : SV Δ) → Si Δ′
  subSV (σ ∷[ i ] i<j) zero    = i
  subSV (σ ∷[ i ] i<j) (suc α) = subSV σ α


  subSi : (σ : SS Δ′ Δ) (i : Si Δ) → Si Δ′
  subSi σ (var α) = subSV σ α
  subSi σ (suc i) = suc (subSi σ i)
  subSi σ ∞ = ∞


variable
  σ τ : SS Δ Δ′


mutual
  renSS : Δ′ ⊇ Δ → SS Δ Ω → SS Δ′ Ω
  renSS θ [] = []
  renSS θ (σ ∷[ i ] i<j) = renSS θ σ ∷[ renSi θ i ] {!!}


  subSi-renSS : subSi (renSS θ σ) j ≡ renSi θ (subSi σ j)
  subSi-renSS = {!!}


  subSV-renSS : subSV (renSS θ σ) α ≡ renSi θ (subSV σ α)
  subSV-renSS = {!!}


⊇→SS : Δ ⊇ Δ′ → SS Δ Δ′
⊇→SS [] = []
⊇→SS (weak θ) = {!subFromRen θ!}
⊇→SS (lift θ p) = {!!}


idS : ∀ Δ → SS Δ Δ
idS [] = []
idS (Δ ∷ i) = {!idS Δ ∷[ ? ] ?!}

{-
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
  _∙_ : {σ τ : SS Δ′ Δ″} {δ δ′ : SS Δ Δ′}
    → σ ≈SS τ
    → δ ≈SS δ′
    → σ ∙ δ ≈SS τ ∙ δ′
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


-- -}
-- -}
-- -}
-- -}
-- -}
