module LamST where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary using
  (Reflexive ; Sym ; Symmetric ; Trans ; Transitive)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl; module ≡-Reasoning)


infix  0 _⊇_
infixl 1 _∷_ _∷[_]_
infixr 2 Π_,_
infixr 3 _⇒_
infixr 5 _∙_ _∙ₛ_


mutual
  -- Size contexts are iterated dependent sums of size bounds.
  data SC : Set where
    [] : SC
    _∷_ : (Δ : SC) (n : Si∞ Δ) → SC


  -- Size variables are indexes into a size context with a given bound.
  data SV : (Δ : SC) → Set where
    zero : ∀ {Δ n} → SV (Δ ∷ n)
    suc : ∀ {Δ n} (α : SV Δ) → SV (Δ ∷ n)


  -- Sizes (without ∞) with variables in a given context.
  data Si Δ : Set where
    var : (α : SV Δ) → Si Δ
    suc : (i : Si Δ) → Si Δ


  -- Sizes (with ∞) with variables in a given context.
  data Si∞ Δ : Set where
    si : (i : Si Δ) → Si∞ Δ
    ∞ : Si∞ Δ


variable
  Δ Δ′ Δ″ : SC
  i j k : Si Δ
  n m o : Si∞ Δ
  α β : SV Δ


mutual
  -- Renamings.
  data _⊇_ : (Δ Δ′ : SC) → Set where
    []   : [] ⊇ []
    weak : (θ : Δ ⊇ Δ′) → Δ ∷ n ⊇ Δ′
    lift : (θ : Δ ⊇ Δ′) (p : renSi∞ θ m ≡ n) → Δ ∷ n ⊇ Δ′ ∷ m


  renSi∞ : Δ ⊇ Δ′ → Si∞ Δ′ → Si∞ Δ
  renSi∞ θ (si i) = si (renSi θ i)
  renSi∞ θ ∞ = ∞


  renSi : Δ ⊇ Δ′ → Si Δ′ → Si Δ
  renSi θ (var α) = var (renSV θ α)
  renSi θ (suc i) = suc (renSi θ i)


  renSV : Δ ⊇ Δ′ → SV Δ′ → SV Δ
  renSV (weak θ)  α        = suc (renSV θ α)
  renSV (lift θ p) zero    = zero
  renSV (lift θ p) (suc α) = suc (renSV θ α)


variable
  θ ι : Δ′ ⊇ Δ


-- K ahoy!
lift-cong : ∀ {p q} → θ ≡ ι → lift {m = m} {n} θ p ≡ lift ι q
lift-cong {p = refl} {refl} refl = refl


mutual
  idR : Δ ⊇ Δ
  idR {[]}    = []
  idR {Δ ∷ i} = lift idR renSi∞-id


  renSi∞-id : renSi∞ idR n ≡ n
  renSi∞-id {n = si i} = ≡.cong si renSi-id
  renSi∞-id {n = ∞} = refl


  renSi-id : renSi idR i ≡ i
  renSi-id {i = var α} = ≡.cong var renSV-id
  renSi-id {i = suc i} = ≡.cong suc renSi-id


  renSV-id : renSV idR α ≡ α
  renSV-id {α = zero}  = refl
  renSV-id {α = suc α} = ≡.cong suc renSV-id


mutual
  _∙_ : Δ ⊇ Δ′ → Δ′ ⊇ Δ″ →  Δ ⊇ Δ″
  [] ∙ ι = ι
  weak θ ∙ ι = weak (θ ∙ ι)
  lift θ p ∙ weak ι = weak (θ ∙ ι)
  lift θ p ∙ lift ι q
    = lift (θ ∙ ι) (≡.trans (≡.trans renSi∞-∙ (≡.cong (renSi∞ θ) q)) p)


  renSi∞-∙ : renSi∞ (θ ∙ ι) n ≡ renSi∞ θ (renSi∞ ι n)
  renSi∞-∙ {n = si i} = ≡.cong si renSi-∙
  renSi∞-∙ {n = ∞} = refl


  renSi-∙ : renSi (θ ∙ ι) i ≡ renSi θ (renSi ι i)
  renSi-∙ {i = var α} = ≡.cong var renSV-∙
  renSi-∙ {i = suc i} = ≡.cong suc renSi-∙


  renSV-∙ : renSV (θ ∙ ι) α ≡ renSV θ (renSV ι α)
  renSV-∙ {θ = []} {ι = []} {()}
  renSV-∙ {θ = weak θ} = ≡.cong suc renSV-∙
  renSV-∙ {θ = lift θ refl} {ι = weak ι} = ≡.cong suc renSV-∙
  renSV-∙ {θ = lift θ refl} {ι = lift ι refl} {zero} = refl
  renSV-∙ {θ = lift θ refl} {ι = lift ι refl} {suc α} = ≡.cong suc renSV-∙


∙-id-l : idR ∙ θ ≡ θ
∙-id-l {θ = []} = refl
∙-id-l {θ = weak θ} = ≡.cong weak ∙-id-l
∙-id-l {θ = lift θ p} = lift-cong ∙-id-l


∙-id-r : θ ∙ idR ≡ θ
∙-id-r {θ = []} = refl
∙-id-r {θ = weak θ} = ≡.cong weak ∙-id-r
∙-id-r {θ = lift θ p} = lift-cong ∙-id-r


weak′ : Δ ∷ n ⊇ Δ
weak′ = weak idR


lift∙weak′ : {θ : Δ ⊇ Δ′} {p : renSi∞ θ n ≡ m} → lift θ p ∙ weak′ ≡ weak θ
lift∙weak′ = ≡.cong weak ∙-id-r


weak′∙ : {θ : Δ ⊇ Δ′} → weak′ {n = n} ∙ θ ≡ weak θ
weak′∙ = ≡.cong weak ∙-id-l


wkSV : SV Δ → SV (Δ ∷ n)
wkSV = renSV weak′


wkSi : Si Δ → Si (Δ ∷ n)
wkSi = renSi weak′


wkSi∞ : Si∞ Δ → Si∞ (Δ ∷ n)
wkSi∞ = renSi∞ weak′


bound : (α : SV Δ) → Si∞ Δ
bound (zero {n = n}) = wkSi∞ n
bound (suc α) = wkSi∞ (bound α)


bound-renSV : bound (renSV θ α) ≡ renSi∞ θ (bound α)
bound-renSV {θ = weak θ} {α} =
  let open ≡-Reasoning in
  begin
    wkSi∞ (bound (renSV θ α))
  ≡⟨ ≡.cong wkSi∞ bound-renSV ⟩
    wkSi∞ (renSi∞ θ (bound α))
  ≡˘⟨ renSi∞-∙ ⟩
    renSi∞ (weak′ ∙ θ) (bound α)
  ≡⟨ ≡.cong (λ z → renSi∞ z (bound α)) weak′∙ ⟩
    renSi∞ (weak θ) (bound α)
  ∎
bound-renSV {θ = lift {m = m} {n} θ p} {zero} =
  let open ≡-Reasoning in
  ≡.sym (begin
    renSi∞ (lift θ p) (wkSi∞ m)
  ≡˘⟨ renSi∞-∙ ⟩
    renSi∞ (lift θ p ∙ weak′) m
  ≡⟨ ≡.cong (λ z → renSi∞ z m) (lift∙weak′ {p = p}) ⟩
    renSi∞ (weak θ) m
  ≡⟨ ≡.cong (λ z → renSi∞ z m) (≡.sym weak′∙) ⟩
    renSi∞ (weak′ ∙ θ) m
  ≡⟨ renSi∞-∙ ⟩
    wkSi∞ (renSi∞ θ m)
  ≡⟨ ≡.cong wkSi∞ p ⟩
    wkSi∞ n
  ∎)
bound-renSV {θ = lift θ p} {suc α} =
  let open ≡-Reasoning in
  begin
    wkSi∞ (bound (renSV θ α))
  ≡⟨ ≡.cong wkSi∞ (bound-renSV) ⟩
    wkSi∞ (renSi∞ θ (bound α))
  ≡˘⟨ renSi∞-∙ ⟩
    renSi∞ (weak′ ∙ θ) (bound α)
  ≡⟨ ≡.cong (λ z → renSi∞ z (bound α)) weak′∙ ⟩
    renSi∞ (weak θ) (bound α)
  ≡⟨ ≡.cong (λ z → renSi∞ z (bound α)) (≡.sym (lift∙weak′ {p = p})) ⟩
    renSi∞ (lift θ p ∙ weak′) (bound α)
  ≡⟨ renSi∞-∙ ⟩
    renSi∞ (lift θ p) (wkSi∞ (bound α))
  ∎


-- TODO better naming in the following
-- TODO redundancy in the definitions of < and ≤?

infix 0  _<_ _≤_


mutual
  -- A preorder on sizes.
  data _≤_ {Δ} : (i j : Si Δ) → Set where
    refl
      : i ≤ i
    <→≤
      : i < j
      → i ≤ j


  -- The obvious extension to sizes with ∞.
  data _≤∞_ {Δ} : (n m : Si∞ Δ) → Set where
    si
      : i ≤ j
      → si i ≤∞ si j
    ∞
      : ∞ ≤∞ ∞


  -- A strict order on sizes.
  data _<_ {Δ} : (i j : Si Δ) → Set where
    var
      : bound α ≡ si i
      → i ≤ j
      → var α < j
    suc
      : i ≤ j
      → i < suc j
    suc-cong
      : i < j
      → suc i < suc j


  -- Its extension to a heterogeneous relation between sizes without and with
  -- ∞.
  data _<∞_ {Δ} : (i : Si Δ) (n : Si∞ Δ) → Set where
    si
      : i < j
      → i <∞ si j
    ∞
      : i <∞ ∞


<-suc′ : i < suc i
<-suc′ = suc refl


mutual
  ≤-suc″ : suc j ≤ k → j ≤ k
  ≤-suc″ refl = <→≤ <-suc′
  ≤-suc″ (<→≤ x) = <→≤ (<-suc″ x)


  <-suc″ : suc j < k → j < k
  <-suc″ (suc x) = suc (≤-suc″ x)
  <-suc″ (suc-cong x) = suc (<→≤ x)


<-suc‴ : suc j ≤ k → j < k
<-suc‴ refl = <-suc′
<-suc‴ (<→≤ Sj<k) = <-suc″ Sj<k


mutual
  ≤→<→< : i ≤ j → j < k → i < k
  ≤→<→< refl j<k = j<k
  ≤→<→< (<→≤ i<j) j<k = <-trans i<j j<k


  <→≤→< : i < j → j ≤ k → i < k
  <→≤→< i<j refl = i<j
  <→≤→< i<j (<→≤ j<k) = <-trans i<j j<k


  <-trans : i < j → j < k → i < k
  <-trans (var bα≡i i≤j) j<k = var bα≡i (<→≤ (≤→<→< i≤j j<k))
  <-trans (suc i≤j) j<k = ≤→<→< i≤j (<-suc″ j<k)
  <-trans (suc-cong i<j) (suc x) = suc-cong (<-trans i<j (<-suc‴ x))
  <-trans (suc-cong i<j) (suc-cong j<k) = suc-cong (<-trans i<j j<k)


  ≤∞-trans : n ≤∞ m → m ≤∞ o → n ≤∞ o
  ≤∞-trans (si i≤j) (si j≤k) = si (≤-trans i≤j j≤k)
  ≤∞-trans ∞ m≤o = m≤o


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


i≰var0 : {j : Si Δ} {i : Si (Δ ∷ n)} → ¬ (i < var zero)
i≰var0 (var x y) = {!y!}


bound≰var : ¬ (bound α ≤∞ si (var α))
bound≰var = {!!}
-- bound≰var {zero {n = si (var α)}} (si (<→≤ x)) = {!!}
-- bound≰var {zero {n = si (suc i)}} (si x) = {!!}
-- bound≰var {suc α} x = {!!}


<∞-var : bound α ≡ n → n ≤∞ m → var α <∞ m
<∞-var bα≡i (si i≤j) = si (<→≤→< (var bα≡i refl) i≤j)
<∞-var bα≡i ∞ = ∞


≤∞-refl : n ≤∞ n
≤∞-refl {n = si i} = si refl
≤∞-refl {n = ∞} = ∞


<∞-var′ : bound α ≡ n → var α <∞ n
<∞-var′ bα≡n = <∞-var bα≡n ≤∞-refl


mutual
  <-asym : i < j → ¬ (j < i)
  <-asym (var bα≡i i≤α) (var bβ≡j j≤α) = {!bβ≤α!}
  <-asym (suc x) (suc x₁) = {!x!}
  <-asym (suc x) (suc-cong x₁) = {!!}
  <-asym (suc-cong x) x₁ = {!!}


  ≤-antisym : i ≤ j → j ≤ i → i ≡ j
  ≤-antisym refl x₁ = refl
  ≤-antisym (<→≤ x) refl = refl
  ≤-antisym (<→≤ x) (<→≤ x₁) = ⊥-elim (<-asym x x₁)


  <-irrefl : ¬ (i < i)
  <-irrefl i<i = <-asym i<i i<i


  ≤→¬> : i ≤ j → ¬ (j < i)
  ≤→¬> refl i<i = <-irrefl i<i
  ≤→¬> (<→≤ j<i) i<j = <-asym i<j j<i


S≤→< : suc i ≤ j → i < j
S≤→< refl = suc refl
S≤→< (<→≤ Si<j) = <-trans (suc refl) Si<j


suc-cong-≤ : i ≤ j → suc i ≤ suc j
suc-cong-≤ refl = refl
suc-cong-≤ (<→≤ i<j) = <→≤ (suc-cong i<j)


mutual
  <→≤S→≤ : i < j → j ≤ suc k → i ≤ k
  <→≤S→≤ i<j refl = <S→≤ i<j
  <→≤S→≤ i<j (<→≤ j<Sk) = <→≤→≤ i<j (<S→≤ j<Sk)


  -- ≤-var : bound α ≡ si i → i ≤ suc j → var α ≤ j
  -- ≤-var bα≡i refl = <S→≤ {!!}
  -- ≤-var bα≡i (<→≤ x) = {!!}


  <S→≤ : i < suc j → i ≤ j
  <S→≤ {j = j} (var {α} bα≡Sj refl) = {!!}
  <S→≤ (var {α} bα≡Sj (<→≤ x)) = {!!} -- ≤-var bα≡Sj (suc-cong-≤ refl)
  <S→≤ (suc x) = x
  <S→≤ (suc-cong x) = {!<→≤ ?!}


  <→S≤ : i < j → suc i ≤ j
  <→S≤ (var x x₁) = {!!}
  <→S≤ (suc x) = {!!}
  <→S≤ (suc-cong x) = {!!}


  <→≤∞→< : i <∞ n → n ≤∞ si j → i ≤ j
  <→≤∞→< i<j j≤k = {!!}


mutual
  renSi-resp-≤ : (θ : Δ′ ⊇ Δ) → i ≤ j → renSi θ i ≤ renSi θ j
  renSi-resp-≤ θ refl = refl
  renSi-resp-≤ θ (<→≤ i<j) = <→≤ (renSi-resp-< θ i<j)


  renSi-resp-< : (θ : Δ′ ⊇ Δ) → i < j → renSi θ i < renSi θ j
  renSi-resp-< {j = j} θ (var {α} bα≡i i≤j)
    = var (≡.trans bound-renSV (≡.cong (renSi∞ θ) bα≡i)) (renSi-resp-≤ θ i≤j)
  renSi-resp-< θ (suc i≤j) = suc (renSi-resp-≤ θ i≤j)
  renSi-resp-< θ (suc-cong i<j) = suc-cong (renSi-resp-< θ i<j)


  renSi∞-resp-≤ : (θ : Δ′ ⊇ Δ) → n ≤∞ m → renSi∞ θ n ≤∞ renSi∞ θ m
  renSi∞-resp-≤ θ (si i≤j) = si (renSi-resp-≤ θ i≤j)
  renSi∞-resp-≤ θ ∞ = ∞


renSi∞-resp-< : (θ : Δ′ ⊇ Δ) → i <∞ n → renSi θ i <∞ renSi∞ θ n
renSi∞-resp-< θ (si i<j) = si (renSi-resp-< θ i<j)
renSi∞-resp-< θ ∞ = ∞


mutual
  -- Size substitutions. SS Δ Δ′ is a morphism from Δ to Δ′, viewing both as
  -- product categories.
  data SS : (Δ Δ′ : SC) → Set where
    [] : SS Δ []
    _∷[_]_
      : (σ : SS Δ Δ′)
      → (i : Si Δ) {n : Si∞ Δ′} (i<n : i <∞ subSi∞ σ n)
      → SS Δ (Δ′ ∷ n)


  subSV : (σ : SS Δ′ Δ) (α : SV Δ) → Si Δ′
  subSV (σ ∷[ i ] i<j) zero    = i
  subSV (σ ∷[ i ] i<j) (suc α) = subSV σ α


  subSi : (σ : SS Δ′ Δ) (i : Si Δ) → Si Δ′
  subSi σ (var α) = subSV σ α
  subSi σ (suc i) = suc (subSi σ i)


  subSi∞ : (σ : SS Δ′ Δ) (n : Si∞ Δ) → Si∞ Δ′
  subSi∞ σ (si i) = si (subSi σ i)
  subSi∞ σ ∞ = ∞


variable
  σ τ : SS Δ Δ′


mutual
  weakS : SS Δ Δ′ → SS (Δ ∷ n) Δ′
  weakS [] = []
  weakS (_∷[_]_ σ i {j} i<j)
    = weakS σ ∷[ wkSi i ]
      ≡.subst (λ z → wkSi i <∞ z) (≡.sym (subSi∞-weakS σ j)) (renSi∞-resp-< weak′ i<j)


  subSi∞-weakS : ∀ (σ : SS Δ Δ′) m
    → subSi∞ (weakS {n = n} σ) m ≡ wkSi∞ (subSi∞ σ m)
  subSi∞-weakS σ (si i) = ≡.cong si (subSi-weakS σ i)
  subSi∞-weakS σ ∞ = refl


  subSi-weakS : ∀ (σ : SS Δ Δ′) i
    → subSi (weakS {n = n} σ) i ≡ wkSi (subSi σ i)
  subSi-weakS σ (var α) = subSV-weakS σ α
  subSi-weakS σ (suc i) = ≡.cong suc (subSi-weakS σ i)


  subSV-weakS :  ∀ (σ : SS Δ Δ′) α
    →  subSV (weakS {n = n} σ) α ≡ wkSi (subSV σ α)
  subSV-weakS (σ ∷[ i ] i<j) zero = refl
  subSV-weakS (σ ∷[ i ] i<j) (suc α) = subSV-weakS σ α


mutual
  idS : SS Δ Δ
  idS {[]} = []
  idS {Δ ∷ n}
    = weakS idS ∷[ var zero ]
      <∞-var′ (≡.sym (≡.trans (subSi∞-weakS idS n) (≡.cong wkSi∞ subSi∞-id)))


  subSi∞-id : subSi∞ idS n ≡ n
  subSi∞-id {n = si i} = ≡.cong si subSi-id
  subSi∞-id {n = ∞} = refl


  subSi-id : subSi idS i ≡ i
  subSi-id {i = var α} = subSV-id
  subSi-id {i = suc i} = ≡.cong suc subSi-id


  subSV-id : subSV idS α ≡ var α
  subSV-id {α = zero} = refl
  subSV-id {α = suc {n = n} α}
    rewrite subSV-weakS {n = n} idS α
          | subSV-id {α = α}
          | renSV-id {α = α}
    = refl


weakS′ : SS (Δ ∷ n) Δ
weakS′ = weakS idS


mutual
  subSi∞-resp-≤ : (σ : SS Δ Δ′) → n ≤∞ m → subSi∞ σ n ≤∞ subSi∞ σ m
  subSi∞-resp-≤ σ (si i≤j) = si (subSi-resp-≤ σ i≤j)
  subSi∞-resp-≤ σ ∞ = ≤∞-refl


  subSi∞-resp-< : (σ : SS Δ Δ′) → i <∞ n → subSi σ i <∞ subSi∞ σ n
  subSi∞-resp-< σ (si i<j) = si (subSi-resp-< σ i<j)
  subSi∞-resp-< σ ∞ = ∞


  subSi-resp-≤ : (σ : SS Δ Δ′) → i ≤ j → subSi σ i ≤ subSi σ j
  subSi-resp-≤ σ refl = refl
  subSi-resp-≤ σ (<→≤ i<j) = <→≤ (subSi-resp-< σ i<j)


  subSi-resp-< : (σ : SS Δ Δ′) → i < j → subSi σ i < subSi σ j
  subSi-resp-< {i = var α} {j} σ i<j = subSV-subSi-resp-< σ i<j
  subSi-resp-< {i = suc i} {suc j} σ (suc Si≤j) = suc-cong (subSi-resp-< σ (S≤→< Si≤j))
  subSi-resp-< {i = suc i} {suc j} σ (suc-cong i<j) = suc-cong (subSi-resp-< σ i<j)


  subSV-subSi-resp-≤ : (σ : SS Δ Δ′) → var α ≤ i → subSV σ α ≤ subSi σ i
  subSV-subSi-resp-≤ σ refl = refl
  subSV-subSi-resp-≤ σ (<→≤ α<i) = <→≤ (subSV-subSi-resp-< σ α<i)


  subSV-subSi-resp-< : (σ : SS Δ Δ′) → var α < i → subSV σ α < subSi σ i
  subSV-subSi-resp-< {i = var β} σ x = subSV-resp-< σ x
  subSV-subSi-resp-< {i = suc i} σ x = suc (subSV-subSi-resp-≤ σ (<S→≤ x))


  subSV-resp-≤ : (σ : SS Δ Δ′) → var α ≤ var β → subSV σ α ≤ subSV σ β
  subSV-resp-≤ σ refl = refl
  subSV-resp-≤ σ (<→≤ α<β) = <→≤ (subSV-resp-< σ α<β)


  subSV-resp-< : (σ : SS Δ Δ′) → var α < var β → subSV σ α < subSV σ β
  subSV-resp-< {α = zero} {zero} (σ ∷[ i ] i<j) z<z = ⊥-elim (<-irrefl z<z)
  subSV-resp-< {α = suc α} {zero} (σ ∷[ i ] i<j) Sα<z = {!!}
  subSV-resp-< {α = zero} {suc β} (σ ∷[ i ] i<j) (var x y) = {!!}
  subSV-resp-< {α = suc α} {suc β} (σ ∷[ i ] i<j) x = {!rrr!} -- subSV-resp-< σ {!!}


mutual
  _∙ₛ_ : (σ : SS Δ′ Δ″) (τ : SS Δ Δ′) → SS Δ Δ″
  [] ∙ₛ τ = []
  (_∷[_]_ σ i {n} i<n) ∙ₛ τ
    = σ ∙ₛ τ ∷[ subSi τ i ]
      ≡.subst (subSi τ i <∞_) (≡.sym (subSi∞-∙ₛ σ τ n)) (subSi∞-resp-< τ i<n)


  subSi∞-∙ₛ : ∀ (σ : SS Δ′ Δ″) (θ : SS Δ Δ′) n
    → subSi∞ (σ ∙ₛ θ) n ≡ subSi∞ θ (subSi∞ σ n)
  subSi∞-∙ₛ σ θ (si i) = ≡.cong si (subSi-∙ₛ σ θ i)
  subSi∞-∙ₛ σ θ ∞ = refl


  subSi-∙ₛ : ∀ (σ : SS Δ′ Δ″) (θ : SS Δ Δ′) i
    → subSi (σ ∙ₛ θ) i ≡ subSi θ (subSi σ i)
  subSi-∙ₛ σ θ (var α) = subSV-∙ₛ σ θ α
  subSi-∙ₛ σ θ (suc i) = ≡.cong suc (subSi-∙ₛ σ θ i)


  subSV-∙ₛ : ∀ (σ : SS Δ′ Δ″) (θ : SS Δ Δ′) α
    → subSV (σ ∙ₛ θ) α ≡ subSi θ (subSV σ α)
  subSV-∙ₛ (σ ∷[ i ] i<n) θ zero = refl
  subSV-∙ₛ (σ ∷[ i ] i<n) θ (suc α) = subSV-∙ₛ σ θ α


liftS : (σ : SS Δ Δ′) → subSi∞ σ m ≡ n → SS (Δ ∷ n) (Δ′ ∷ m)
liftS σ refl = weakS σ ∷[ (var zero) ] (<∞-var′ {!!})


mutual
  ⊇→SS : Δ ⊇ Δ′ → SS Δ Δ′
  ⊇→SS [] = []
  ⊇→SS (weak θ) = ⊇→SS θ ∙ₛ weakS′
  ⊇→SS (lift θ p) = liftS (⊇→SS θ) (≡.trans (subSi∞-⊇→SS θ _) p)


  subSi∞-⊇→SS : ∀ (θ : Δ ⊇ Δ′) n
    → subSi∞ (⊇→SS θ) n ≡ renSi∞ θ n
  subSi∞-⊇→SS = {!!}


  subSi-⊇→SS : ∀ (θ : Δ ⊇ Δ′) i
    → subSi (⊇→SS θ) i ≡ renSi θ i
  subSi-⊇→SS = {!!}


  subSV-⊇→SS : ∀ (θ : Δ ⊇ Δ′) α
    → subSV (⊇→SS θ) α ≡ var (renSV θ α)
  subSV-⊇→SS = {!!}


mutual
  _ₛ∙ᵣ_ : (σ : SS Δ′ Δ″) (θ : Δ ⊇ Δ′) → SS Δ Δ″
  [] ₛ∙ᵣ θ = []
  (_∷[_]_ σ i {j} i<j) ₛ∙ᵣ θ
    = (σ ₛ∙ᵣ θ) ∷[ renSi θ i ]
      ≡.subst (renSi θ i <∞_) (≡.sym (subSi∞-ₛ∙ᵣ σ θ j)) (renSi∞-resp-< θ i<j)


  subSi∞-ₛ∙ᵣ : ∀ (σ : SS Δ′ Δ″) (θ : Δ ⊇ Δ′) n
    → subSi∞ (σ ₛ∙ᵣ θ) n ≡ renSi∞ θ (subSi∞ σ n)
  subSi∞-ₛ∙ᵣ σ θ (si i) = ≡.cong si (subSi-ₛ∙ᵣ σ θ i)
  subSi∞-ₛ∙ᵣ σ θ ∞ = refl


  subSi-ₛ∙ᵣ : ∀ (σ : SS Δ′ Δ″) (θ : Δ ⊇ Δ′) j
    → subSi (σ ₛ∙ᵣ θ) j ≡ renSi θ (subSi σ j)
  subSi-ₛ∙ᵣ σ θ (var α) = subSV-ₛ∙ᵣ σ θ α
  subSi-ₛ∙ᵣ σ θ (suc j) = ≡.cong suc (subSi-ₛ∙ᵣ σ θ j)


  subSV-ₛ∙ᵣ : ∀ (σ : SS Δ′ Δ″) (θ : Δ ⊇ Δ′) α
    → subSV (σ ₛ∙ᵣ θ) α ≡ renSi θ (subSV σ α)
  subSV-ₛ∙ᵣ (σ ∷[ i ] i<j) θ zero = refl
  subSV-ₛ∙ᵣ (σ ∷[ i ] i<j) θ (suc α) = subSV-ₛ∙ᵣ σ θ α


-- Types.
data Ty Δ : Set where
  ℕ : (i : Si Δ) → Ty Δ
  _⇒_ : (T U : Ty Δ) → Ty Δ
  Π_,_ : (n : Si∞ Δ) (T : Ty (Δ ∷ n)) → Ty Δ


subTy : (σ : SS Δ′ Δ) (T : Ty Δ) → Ty Δ′
subTy σ (ℕ i) = ℕ (subSi σ i)
subTy σ (T ⇒ U) = subTy σ T ⇒ subTy σ U
subTy σ (Π i , T) = Π subSi∞ σ i , subTy (liftS σ refl) T


-- Type contexts.
data TC Δ : Set where
  [] : TC Δ
  _∷_ : (Γ : TC Δ) (T : Ty Δ) → TC Δ


variable
  Γ Γ′ Γ″ : TC Δ


{-
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
