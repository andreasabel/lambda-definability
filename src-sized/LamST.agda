module LamST where

open import Relation.Binary using
  (Reflexive ; Sym ; Symmetric ; Trans ; Transitive)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl; module ≡-Reasoning)


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
  Δ Δ′ Δ″ Ω : SC
  i j k : Si Δ
  α β : SV Δ


mutual
  infix 0 _⊇_
  data _⊇_ : (Δ Δ′ : SC) → Set where
    []   : [] ⊇ []
    weak : (i : Si Δ) (τ : Δ ⊇ Δ′) → Δ ∷ i ⊇ Δ′
    lift : (i′ : Si Δ′) (τ : Δ ⊇ Δ′) (p : renSi τ i′ ≡ i) → Δ ∷ i ⊇ Δ′ ∷ i′

  renSi : (τ : Δ ⊇ Δ′) → Si Δ′ → Si Δ
  renSi τ (var α) = var (renSV τ α)
  renSi τ (suc i) = suc (renSi τ i)
  renSi τ ∞       = ∞

  renSV : Δ ⊇ Δ′ → SV Δ′ → SV Δ
  renSV (weak i τ)  α       = suc (renSV τ α)
  renSV (lift i′ τ p) zero    = zero
  renSV (lift i′ τ p) (suc α) = suc (renSV τ α)

variable
  τ τ′ : Δ′ ⊇ Δ

cong-lift : ∀ p p′ → τ ≡ τ′ → lift {_} {_} {j} i τ p ≡ lift i τ′ p′
cong-lift refl refl refl = refl

mutual
  idR : ∀ Δ → Δ ⊇ Δ
  idR []      = []
  idR (Δ ∷ i) = lift i (idR Δ) (renSi-id i)

  renSi-id : ∀ i → renSi (idR Δ) i ≡ i
  renSi-id (var α) = ≡.cong var (renSV-id α)
  renSi-id (suc i) = ≡.cong suc (renSi-id i)
  renSi-id ∞       = refl

  renSV-id : ∀ (α : SV Δ) → renSV (idR Δ) α ≡ α
  renSV-id zero    = refl
  renSV-id (suc α) = ≡.cong suc (renSV-id α)

-- lift-id-refl : lift i (idR Δ) refl ≡ ≡.subst (λ j → Δ ∷ j ⊇ Δ ∷ i) (≡.sym (renSi-id i)) (idR (Δ ∷ i)) -- idR (Δ ∷ renSi (idR Δ) i)
-- lift-id-refl {i = i} = {!!}

-- lift-id : (p : renSi (idR Δ) i ≡ j) →
--           lift i (idR Δ) p ≡ ≡.subst (λ j → Δ ∷ j ⊇ Δ ∷ i) (≡.trans (≡.sym (renSi-id i)) p) (idR (Δ ∷ i)) -- idR (Δ ∷ renSi (idR Δ) i)
-- lift-id refl = {!!}

mutual
  ren-ren : Δ ⊇ Δ′ → Δ′ ⊇ Δ″ →  Δ ⊇ Δ″
  ren-ren [] τ′ = τ′
  ren-ren (weak i τ) τ′ = weak i (ren-ren τ τ′)
  ren-ren (lift i τ p) (weak .i τ′) = weak _ (ren-ren τ τ′)
  ren-ren (lift i τ p) (lift i′ τ′ p′) = lift _ (ren-ren τ τ′) (≡.trans (≡.trans (ren-renSi _) (≡.cong (renSi τ) p′)) p)
  -- ren-ren (lift i τ p) (lift i′ τ′ refl) = lift _ (ren-ren τ τ′) (≡.trans (ren-renSi _) p)
  -- ren-ren (lift i τ refl) (lift i′ τ′ refl) = lift _ (ren-ren τ τ′) (ren-renSi _)

  ren-renSi : ∀ i → renSi (ren-ren τ τ′) i ≡ renSi τ (renSi τ′ i)
  ren-renSi (var α) = ≡.cong var (ren-renSV _ _ α)
  ren-renSi (suc i) = ≡.cong suc (ren-renSi i)
  ren-renSi ∞ = refl

  ren-renSV : ∀ (τ : Δ ⊇ Δ′) (τ′ : Δ′ ⊇ Δ″) α → renSV (ren-ren τ τ′) α ≡ renSV τ (renSV τ′ α)
  ren-renSV _ [] ()
  ren-renSV (weak i τ) τ′ α = ≡.cong suc (ren-renSV τ τ′ α)
  ren-renSV (lift i′ τ refl) (weak .i′ τ′) α = ≡.cong suc (ren-renSV τ τ′ α)
  ren-renSV (lift i′ τ refl) (lift i′₁ τ′ refl) zero = refl
  ren-renSV (lift i′ τ refl) (lift i′₁ τ′ refl) (suc α) = ≡.cong suc (ren-renSV τ τ′ α)

ren-id-l : ∀ Δ {τ : Δ ⊇ Δ′} → ren-ren (idR Δ) τ ≡ τ
ren-id-l [] = refl
ren-id-l (Δ ∷ i) {weak .i τ}   = ≡.cong (weak i) (ren-id-l Δ)
ren-id-l (Δ ∷ i) {lift i′ τ p} = cong-lift _ _ (ren-id-l Δ)

ren-id-r : ∀ (τ : Δ′ ⊇ Δ) → ren-ren τ (idR Δ) ≡ τ
ren-id-r []            = refl
ren-id-r (weak i τ)    = ≡.cong (weak i) (ren-id-r _)
ren-id-r (lift i′ τ p) = cong-lift _ _ (ren-id-r _)

lift-weak-id : (p : renSi τ i ≡ j) → ren-ren (lift i τ p) (weak i (idR Δ))  ≡ weak j τ
lift-weak-id refl = ≡.cong (weak _) (ren-id-r _)

ren-ren-weak-id : ren-ren (weak i (idR Δ)) τ  ≡ weak i τ
ren-ren-weak-id = ≡.cong (weak _) (ren-id-l _)

{-
mutual
  infix 0 _⊇_
  data _⊇_ : (Δ Δ′ : SC) → Set where
    []   : [] ⊇ []
    weak : (i  : Si Δ ) (τ : Δ ⊇ Δ′) → Δ ∷ i ⊇ Δ′
    lift : (i′ : Si Δ′) (τ : Δ ⊇ Δ′) (let i = renSi τ i′) → Δ ∷ i ⊇ Δ′ ∷ i′

  renSi : (τ : Δ ⊇ Δ′) → Si Δ′ → Si Δ
  renSi τ (var α) = var (renSV τ α)
  renSi τ (suc i) = suc (renSi τ i)
  renSi τ ∞       = ∞

  renSV : Δ ⊇ Δ′ → SV Δ′ → SV Δ
  renSV (weak i τ)  α       = suc (renSV τ α)
  renSV (lift i′ τ) zero    = zero
  renSV (lift i′ τ) (suc α) = suc (renSV τ α)

mutual
  idR : ∀ Δ → Δ ⊇ Δ
  idR []      = []
  idR (Δ ∷ i) = ≡.subst (λ z → Δ ∷ z ⊇ Δ ∷ i)(renSi-id Δ i) (lift i (idR Δ))

  renSi-id : ∀ Δ i → renSi (idR Δ) i ≡ i
  renSi-id Δ (var α) = ≡.cong var (renSV-id Δ α)
  renSi-id Δ (suc i) = ≡.cong suc (renSi-id Δ i)
  renSi-id Δ ∞       = refl

  renSV-id : ∀ Δ (α : SV Δ) → renSV (idR Δ) α ≡ α
  renSV-id (Δ ∷ i) zero    = {!!} -- rewrite renSi-id Δ i = {!!}
  renSV-id (Δ ∷ i) (suc α) = {!aux (idR Δ) (renSi (idR Δ) i) (renSi-id Δ i)!}
    where
    aux : ∀ {Δ} {i : Si Δ} {α : SV Δ} (τ : Δ ⊇ Δ) (w₁ : Si Δ)
        (w₂ : w₁ ≡ renSi τ i) →
      renSV (≡.subst (λ z → Δ ∷ z ⊇ Δ ∷ i) w₂ (lift i τ)) (suc α) ≡ suc α
    aux _ _ _ = ?
{-
    aux : ∀ {Δ} {i : Si Δ} {α : SV Δ} (w : Si Δ) (w₁ : w ≡ i) →
      renSV (≡.subst (λ z → Δ ∷ z ⊇ Δ ∷ i) w₁ (lift i (idR Δ))) (suc α) ≡
      suc α
    aux {Δ} .(idR Δ) refl = ?
{-
    aux : ∀ {Δ} w (w₁ : Δ ⊇ Δ) (i : Si Δ) (w₂ : w w₁ i ≡ i)
        {α : SV Δ} →
      renSV (≡.subst (λ z → Δ ∷ z ⊇ Δ ∷ i) w₂ (lift i w₁)) (suc α) ≡
      suc α
    aux w τ i refl = ?
{-
    aux : ∀ {Δ} {i : Si Δ} (w : renSi (idR Δ) i ≡ i) {α : SV Δ} →
      renSV (≡.subst (λ z → Δ ∷ z ⊇ Δ ∷ i) w (lift i (idR Δ))) (suc α) ≡
      suc α
    aux refl = ?
    -- aux : ∀ {Δ} {i : Si Δ} {α : SV Δ} →
    --   renSV
    --   (≡.subst (λ z → Δ ∷ z ⊇ Δ ∷ i) (lift i (idR Δ)))
    --   (suc α)
    --   ≡ suc α
-}
-}
-}
-}

wkSV : SV Δ → SV (Δ ∷ i)
wkSV = renSV (weak _ (idR _))

{-
wkSV : SV Δ → SV (Δ ∷ i)
wkSV zero = suc zero
wkSV (suc α) = suc (wkSV α)
-}

wkSi : Si Δ → Si (Δ ∷ i)
wkSi = renSi (weak _ (idR _))
{-
wkSi : Si Δ → Si (Δ ∷ i)
wkSi (var α) = var (wkSV α)
wkSi (suc i) = suc (wkSi i)
wkSi ∞ = ∞
-}

bound : (α : SV Δ) → Si Δ
bound (zero {i = i}) = wkSi i
bound (suc α) = wkSi (bound α)


bound-wkSV : (α : SV Δ) → bound (wkSV {i = i} α) ≡ wkSi (bound α)
bound-wkSV zero = refl
bound-wkSV (suc α) = ≡.cong wkSi (bound-wkSV α)

ren-bound : ∀ (τ : Δ′ ⊇ Δ) α → renSi τ (bound α) ≡ bound (renSV τ α)
ren-bound (weak i τ)    α = begin
  renSi (weak i τ) (bound α)                    ≡⟨ ≡.cong (λ z → renSi z (bound α)) (≡.sym ren-ren-weak-id) ⟩
  renSi (ren-ren (weak _ (idR _)) τ) (bound α)  ≡⟨ ren-renSi (bound α) ⟩
  wkSi (renSi τ (bound α))                      ≡⟨ ≡.cong wkSi (ren-bound τ α) ⟩
  wkSi (bound (renSV τ α))
  ∎ where open ≡-Reasoning
ren-bound (lift i′ τ p) α = {!!}

ren-bound (weak i τ) (zero {i = j}) = begin
  renSi (weak i τ) (wkSi j)                    ≡⟨ ≡.cong (λ z → renSi (weak i z) (wkSi j)) (≡.sym (ren-id-l _)) ⟩
  renSi (ren-ren (weak i (idR _)) τ) (wkSi _)  ≡⟨ ren-renSi _ ⟩
  wkSi (renSi τ (wkSi _))                      ≡⟨ ≡.cong wkSi (ren-bound τ zero) ⟩
  wkSi (bound (renSV τ zero))
  ∎ where open ≡-Reasoning

ren-bound (lift i′ τ refl) zero = begin
  renSi (lift i′ τ refl) (renSi (weak i′ (idR _)) i′)   ≡⟨  ≡.sym (ren-renSi i′) ⟩
  renSi (ren-ren (lift i′ τ refl) (weak i′ (idR _))) i′ ≡⟨  ≡.cong (λ z → renSi (weak (renSi τ i′) z) i′) (≡.trans (ren-id-r _) (≡.sym (ren-id-l _))) ⟩
  renSi (ren-ren (weak (renSi τ i′) (idR _)) τ) i′      ≡⟨  ren-renSi i′ ⟩
  renSi (weak (renSi τ i′) (idR _)) (renSi τ i′)
  ∎ where open ≡-Reasoning
ren-bound (weak i τ) (suc α) = {!!}
ren-bound (lift i′ τ p) (suc α) = {!!}

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
  ren-≤ : (τ : Δ′ ⊇ Δ) → i ≤ j → renSi τ i ≤ renSi τ j
  ren-≤ τ refl = refl
  ren-≤ τ (<→≤ i<j) = <→≤ (ren-< τ i<j)

  ren-< : (τ : Δ′ ⊇ Δ) → i < j → renSi τ i < renSi τ j
  ren-< τ (var {zero} x) = var {!ren-< τ x!}
  ren-< τ (var {suc α} x) = var {!!}
  ren-< τ (suc i≤j) = suc (ren-≤ τ i≤j)
  ren-< τ (suc-cong i<j) = suc-cong (ren-< τ i<j)
  ren-< τ ∞ = ∞


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
  σ σ′ : SS Δ Δ′

mutual
  renSS : Δ′ ⊇ Δ → SS Δ Ω → SS Δ′ Ω
  renSS τ [] = []
  renSS τ (σ ∷[ i ] i<j) = renSS τ σ ∷[ renSi τ i ] {!!}

  subSi-renSS : subSi (renSS τ σ) j ≡ renSi τ (subSi σ j)
  subSi-renSS = {!!}

  subSV-renSS : subSV (renSS τ σ) α ≡ renSi τ (subSV σ α)
  subSV-renSS = {!!}

subFromRen : Δ ⊇ Δ′ → SS Δ Δ′
subFromRen [] = []
subFromRen (weak i τ) = {!subFromRen τ!}
subFromRen (lift i′ τ p) = {!!}

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


-- -}
-- -}
-- -}
-- -}
-- -}
