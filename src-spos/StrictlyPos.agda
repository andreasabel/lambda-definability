{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

module StrictlyPos where

open import Library

subst-trans : ∀ {A : Set}{P : A → Set} {x y z : A} →
                (p : x ≡ y) → (q : y ≡ z) → (xs : P x) →
                  subst P (trans p q) xs ≡ subst P q (subst P p xs)
subst-trans refl refl xs = refl

-- _S_trictly _P_ositive functors have a well-behaved support

_→̇_ : {I : Set} (A B : I → Set) → Set
A →̇ B = ∀{i} (u : A i) → B i

record SPos (I : Set) : Set₁ where
  field
    F    : (ρ : I → Set) → Set
    mon  : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') (x : F ρ) → F ρ'
    mon-id : ∀{ρ}  → mon {ρ} id ≡ id

    Supp : ∀{ρ} (x : F ρ) (i : I) → Set

    mon-Supp : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') (x : F ρ) → Supp (mon ρ→ρ' x) →̇ Supp x
    mon-Supp-id : ∀{ρ} (x : F ρ) → (λ{i} → mon-Supp {ρ} id x {i}) ≡  λ{i} → subst (λ f → Supp (f x) i) (mon-id {ρ})

    necc : ∀{ρ} (x : F ρ) → Supp x →̇ ρ
    suff : ∀{ρ} (x : F ρ) → F (Supp x)

    mon-Supp-suff : ∀{ρ ρ'} (x : F ρ) (supp→ρ' : Supp x →̇ ρ') → Supp (mon supp→ρ' (suff x)) →̇ Supp x


    -- laws
    mon-∙ : ∀ {x y z} {g : y →̇  z} {f : x →̇  y} →
            ∀ xs → mon {y} {z} g (mon f xs) ≡ mon (g ∘ f) xs

    necc-suff : ∀ {ρ} {x : F ρ} →  mon (necc x) (suff x) ≡ x

{-

    mon-Supp-∙ : ∀ {x y z} {g : y → z} {f : x → y} →
                 ∀ xs → (p : Supp (mon g (mon f xs)))
                 → mon-Supp f xs (mon-Supp g (mon f xs) p)
                 ≡ mon-Supp (g ∘ f) xs (subst Supp (mon-∙ xs) p)


    necc-nat : ∀{ρ ρ' : Set} → (f : ρ → ρ') → ∀ (xs : F ρ) (p : Supp (mon f xs))
               → necc (mon f xs) p ≡ f (necc xs (mon-Supp f xs p))

    suff-nat : ∀{ρ ρ'} → (f : ρ → ρ') → ∀ (xs : F ρ)
               → mon (mon-Supp f xs) (suff (mon f xs)) ≡ suff xs


    suff-necc : ∀ {ρ} {x : F ρ} (p : Supp _)
                → necc (suff x) (mon-Supp (necc x) (suff x) p)
                ≡ subst Supp necc-suff p
-}
open SPos

-- Constructions on SPos

SP = SPos ∘ Fin

-- Variable

δ-diag : ∀{n} (i : Fin n) → δ i i ≡ ⊤
δ-diag zero = refl
δ-diag (suc i) with i ≟ i
δ-diag (suc i) | yes p = refl
δ-diag (suc i) | no ¬p = case ¬p refl of λ()

-- {-# REWRITE δ-diag #-}  -- illegal

-- Type variables (projections)

-- Var could be generalized to decidable I

Var : ∀{n} (i : Fin n) → SP n
Var i .F ρ = ρ i
Var i .mon ρ→ρ' x = ρ→ρ' x
Var i .mon-id = refl
Var i .Supp _ j = δ i j
Var i .mon-Supp ρ→ρ' _ = id
Var i .mon-Supp-id {ρ} x = refl
Var i .necc x {j} u with i ≟ j
Var i .necc x {.i} _ | yes refl = x
Var i .necc x {j} () | no _
Var i .suff = _ -- rewrite δ-diag i = _
Var i .mon-Supp-suff x supp→ρ' u = u

-- Constant types have empty support

Const : ∀ (A : Set) {I} → SPos I
Const A .F _ = A
Const A .mon _ = id
Const A .mon-id = refl
Const A .Supp _ _ = ⊥
Const A .mon-Supp _ _ = id
Const A .mon-Supp-id x = refl
Const A .necc _ ()
Const A .suff = id
Const A .mon-Supp-suff _ _ = id

Empty = Const ⊥
Unit  = Const ⊤

-- Empty : ∀{I} → SPos I
-- Empty .F _ = ⊥
-- Empty .mon _ ()
-- Empty .Supp ()
-- Empty .mon-Supp _ ()
-- Empty .necc ()
-- Empty .suff ()

-- Unit : ∀{I} → SPos I
-- Unit .F _ = ⊤
-- Unit .mon = _
-- Unit .Supp _ _ = ⊥
-- Unit .mon-Supp ρ→ρ' _ ()
-- Unit .necc _ ()
-- Unit .suff = _

Fun : ∀ (A : Set) {I} (B : SPos I) → SPos I
Fun A B .F ρ                     = A → B .F ρ
Fun A B .mon ρ→ρ' f a            = B .mon ρ→ρ' (f a)
Fun A B .mon-id                 =  funExt λ f → funExt λ a → cong-app (B .mon-id) (f a)
Fun A B .Supp f i                = ∃ λ (a : A) → B .Supp (f a) i
Fun A B .mon-Supp ρ→ρ' f (a , u) = a , B .mon-Supp ρ→ρ' (f a) u
-- Fun A B .mon-Supp-id {ρ} f = funExtH λ{i} →  funExt λ p → {! aux (B .mon {ρ} id) (B .mon-id {ρ})!}
--   where
--   aux : ∀ {A I} {B : SPos I} {ρ : I → Set} {f : A → B .F ρ} {i : I}
--         {p : ∃ (λ a → B .Supp (B .mon (λ {i₁} → id) (f a)) i)}
--         (w : B .F ρ → B .F ρ) (w₁ : w ≡ (λ x → x)) →
--       (p .proj₁ , B .mon-Supp (λ {i₁} x → x) (f (p .proj₁)) (p .proj₂)) ≡
--       subst (λ f₁ → Σ A (λ a → B .Supp (f₁ f a) i))
--       (funExt (λ f₁ → funExt (λ a → cong-app w₁ (f₁ a)))) p
--   aux = ?
  -- aux : ∀ {A I} {B : SPos I} {ρ : I → Set} {f : A → B .F ρ} {i : I}
  --       {a : A} {u : B .Supp (B .mon (λ {i₁} → id) (f a)) i}
  --       (w : B .F ρ → B .F ρ) (w₁ : w ≡ (λ x → x)) →
  --     (a , B .mon-Supp (λ {i₁} x → x) (f a) u) ≡
  --     subst (λ f₁ → Σ A (λ a₁ → B .Supp (f₁ f a₁) i))
  --     (funExt (λ f₁ → funExt (λ a₁ → cong-app w₁ (f₁ a₁)))) (a , u)
  -- aux = ?
  -- aux : ∀ {i}
  --       {a : A}
  --       (w : B .F ρ → B .F ρ)  {u : B .Supp (w (f a)) i} (w₁ : w ≡ id) →
  --     (a , B .mon-Supp id (f a) u) ≡
  --     subst (λ f₁ → Σ A (λ a₁ → B .Supp (f₁ f a₁) i))
  --     (funExt (λ f₁ → funExt (λ a₁ → cong-app w₁ (f₁ a₁)))) (a , u)
  -- aux = ?
Fun A B .mon-Supp-id {ρ} f = funExtH λ{i} →  funExt λ{ (a , u) → {! aux (B .mon {ρ} id) (B .mon-id {ρ}) (B .mon-Supp {ρ} id) (B .mon-Supp-id {ρ} (f a))!} }
  -- where
  -- aux : ∀ {A I} {B : SPos I} {ρ : I → Set} {f : A → B .F ρ} {i : I}
  --       {a : A} {u : B .Supp (B .mon (λ {i₁} → id) (f a)) i}
  --       (w : B .F ρ → B .F ρ) (w₁ : w ≡ (λ x → x))
  --       (w₂
  --        : (x : B .F ρ) {i : I} → B .Supp (w x) i → B .Supp x i) →
  --     (λ{i₁} → w₂ (f a) {i₁}) ≡ (λ {i₁} → subst (λ f₁ → B .Supp (f₁ (f a)) i₁) w₁) →
  --     (a , w₂ (f a) u) ≡
  --     subst (λ f₁ → Σ A (λ a₁ → B .Supp (f₁ f a₁) i))
  --     (funExt (λ f₁ → funExt (λ a₁ → cong-app w₁ (f₁ a₁)))) (a , u)
  -- aux = ?
-- Fun A B .mon-Supp-id {ρ} f = {! aux (B .mon {ρ} id) (B .mon-id {ρ}) (Fun A B .mon-Supp {ρ} id)!}
-- Fun A B .mon-Supp-id {ρ} f with B .mon {ρ} id | B .mon-id {ρ} | B .mon-Supp {ρ} id
-- ... | z | eq | u = {!eq!}
-- Fun A B .mon-Supp-id {ρ} f rewrite B .mon-id {ρ} = {!!}
Fun A B .necc f (a , u)          = B .necc (f a) u
Fun A B .suff f a                = B .mon (a ,_) (B .suff (f a))
Fun A B .mon-Supp-suff f supp→ρ' (a , u) = a , B .mon-Supp-suff (f a) (λ{i} u → supp→ρ' (a , u)) {!u!}

Prod : ∀{I} (A B : SPos I) → SPos I
Prod A B .F ρ                            = A .F ρ × B .F ρ
Prod A B .mon ρ→ρ' (a , b)               = A .mon ρ→ρ' a , B .mon ρ→ρ' b
Prod A B .mon-id                         =  cong₂ _×̇_ (A .mon-id) (B .mon-id)
Prod A B .Supp (a , b) i                 = A .Supp a i ⊎ B .Supp b i
Prod A B .mon-Supp ρ→ρ' (a , b) (inj₁ u) = inj₁ (A .mon-Supp ρ→ρ' a u)
Prod A B .mon-Supp ρ→ρ' (a , b) (inj₂ u) = inj₂ (B .mon-Supp ρ→ρ' b u)
Prod A B .mon-Supp-id {ρ} (a , b) = {!!}
-- Prod A B .mon-Supp-id {ρ} (a , b) rewrite A .mon-id {ρ} = {!!}
Prod A B .necc (a , b) (inj₁ u)          = A .necc a u
Prod A B .necc (a , b) (inj₂ u)          = B .necc b u
Prod A B .suff (a , b)                   = A .mon inj₁ (A .suff a) , B .mon inj₂ (B .suff b)
Prod A B .mon-Supp-suff (a , b) supp→ρ' (inj₁ u) = inj₁ (A .mon-Supp-suff a (λ{i} u' → supp→ρ' (inj₁ u')) {!!})
Prod A B .mon-Supp-suff (a , b) supp→ρ' (inj₂ u) = {!!}

Sum : ∀{I} (A B : SPos I) → SPos I
Sum A B .F ρ                      = A .F ρ ⊎ B .F ρ
Sum A B .mon ρ→ρ' (inj₁ a)        = inj₁ (A .mon ρ→ρ' a)
Sum A B .mon ρ→ρ' (inj₂ b)        = inj₂ (B .mon ρ→ρ' b)
Sum A B .mon-id                   =  funExt λ
  { (inj₁ a) → cong (λ f → inj₁ (f a)) (A .mon-id)
  ; (inj₂ b) → cong (λ f → inj₂ (f b)) (B .mon-id)
  }
-- Sum A B .mon-id (inj₁ a)          = {! cong inj₁ (A .mon-id a) !}
-- Sum A B .mon-id (inj₂ b)          = {! cong inj₂ (B .mon-id b) !}
Sum A B .Supp (inj₁ a) i          = A .Supp a i
Sum A B .Supp (inj₂ b) i          = B .Supp b i
Sum A B .mon-Supp ρ→ρ' (inj₁ a) u = A .mon-Supp ρ→ρ' a u
Sum A B .mon-Supp ρ→ρ' (inj₂ b) u = B .mon-Supp ρ→ρ' b u
Sum A B .mon-Supp-id {ρ} (inj₁ a) = {!!}
-- with A .mon {ρ} id | A .mon-id {ρ} | A .mon-Supp id a | A .mon-Supp-id {ρ} a
-- ... | x | y | z | v = {!!}
-- Sum A B .mon-Supp-id {ρ} (inj₁ a) rewrite A .mon-id {ρ} | A .mon-Supp-id {ρ} a = {!!}
Sum A B .necc (inj₁ a) u          = A .necc a u
Sum A B .necc (inj₂ b) u          = B .necc b u
Sum A B .suff (inj₁ a)            = inj₁ (A .suff a)
Sum A B .suff (inj₂ b)            = inj₂ (B .suff b)
Sum A B .mon-Supp-suff (inj₁ a) supp→ρ' u = A .mon-Supp-suff a supp→ρ' u
Sum A B .mon-Supp-suff (inj₂ b) supp→ρ' u = B .mon-Supp-suff b supp→ρ' u

ext : ∀{ℓ} {A : Set ℓ} {n} (ρ : Fin n → A) (x : A) (i : Fin (suc n)) → A
ext ρ x zero = x
ext ρ x (suc i) = ρ i

ext-⊤-mon : ∀{n}{ρ ρ' : Fin n → Set} (ρ→ρ' : ρ →̇ ρ') → ext ρ ⊤ →̇ ext ρ' ⊤
ext-⊤-mon ρ→ρ' {zero} = _
ext-⊤-mon ρ→ρ' {suc i} = ρ→ρ'

-- ext-⊤-mon-id : ∀{n} {ρ : Fin n → Set} → _≡_ {A = ext ρ ⊤ →̇ ext ρ ⊤} (λ{i} → ext-⊤-mon {n} {ρ} id {i}) id
ext-⊤-mon-id : ∀{n} {ρ : Fin n → Set} → (λ{i} → ext-⊤-mon {n} {ρ} id {i}) ≡ id
ext-⊤-mon-id = funExtH λ{ {zero} → refl ; {suc i} → refl }

{-# REWRITE ext-⊤-mon-id #-}

{-# TERMINATING #-}
Mu : ∀{n} (A : SP (suc n)) → SP n
Mu A .F ρ  = 𝕎 (A .F (ext ρ ⊤)) λ x → A .Supp x zero
Mu A .mon {ρ}{ρ'} ρ→ρ' = 𝕎-map (A .mon λ{i} → ext-⊤-mon ρ→ρ' {i})
                                (λ x → A .mon-Supp (λ{i} → ext-⊤-mon ρ→ρ' {i}) x)
-- Mu A .mon-id {ρ} (sup x f) = {!!}
Mu A .mon-id {ρ} with A .mon {ext ρ ⊤} id | A .mon-id {ext ρ ⊤} | A .mon-Supp {ext ρ ⊤} id
Mu A .mon-id {ρ} | .id | refl | v = {!!} -- with A .mon-id x
-- Mu A .mon-id {ρ} (sup x f) with A .mon {ext ρ ⊤} id | A .mon-id {ext ρ ⊤} | A .mon-Supp {ext ρ ⊤} id
-- ... | t | u | v = {!!} -- with A .mon-id x
-- = hcong₂ sup (A .mon-id x) {!!} -- rewrite A .mon-id x = {!hcong₂ sup ? ?!}
Mu A .Supp w i = EF𝕎 (λ x → A .Supp x (suc i)) w
Mu A .mon-Supp ρ→ρ' (sup x f) (here p)    = here (A .mon-Supp (λ{i} → ext-⊤-mon ρ→ρ' {i}) x p)
Mu A .mon-Supp ρ→ρ' (sup x f) (there i u) = there v (Mu A .mon-Supp ρ→ρ' (f v) u)
  where
  v : A .Supp x zero
  v = A .mon-Supp (λ {j} → ext-⊤-mon ρ→ρ' {j}) x i
Mu A .necc (sup x f) (here p)    = A .necc x p
Mu A .necc (sup x f) (there i u) = Mu A .necc (f i) u
Mu A .suff {ρ} (sup x f) = sup x' \ p →
  let
    r : 𝕎 (A .F (ext ρ ⊤)) (λ x₁ → A .Supp x₁ zero)
    r = f (A .mon-Supp-suff x ζ p)
  in
      𝕎-map (A .mon (\ {i} → α p i))
        (β {p}) (Mu A .suff r)
  where
  ζ : A .Supp x →̇ ext (Mu A .Supp (sup x f)) ⊤
  ζ {zero} = _
  ζ {suc i} = here

  -- agda was not happy about i being implicit when applying alpha
  α : ∀ p → ∀ i
      → ext (Mu A .Supp (f (A .mon-Supp-suff x ζ p))) ⊤ i
      → ext (Mu A .Supp (sup x f))                    ⊤ i
  α p i = ext-⊤-mon (there (A .mon-Supp-suff x ζ p)) {i}


  β : ∀ {p : A .Supp (A .mon ζ (A .suff x)) zero}
        (s : A .F (ext (Mu A .Supp (f (A .mon-Supp-suff x ζ p))) ⊤))
      → A .Supp (A .mon (\ {i} → α p i) s) zero
      → A .Supp s                          zero
  β {p} s q = A .mon-Supp-suff s _ q''
    where
      q' = subst (\ s → A .Supp (A .mon ((λ {i} → α p i)) s) zero) (sym (A .necc-suff)) q
      q'' = subst (\ s → A .Supp s zero) (A .mon-∙ (A .suff s)) q'

  x' : A .F (ext (Mu A .Supp (sup x f)) ⊤)
  x' = A .mon ζ (A .suff x)

{-
-- containers
record Cont : Set₁ where
  constructor _,_
  field
    S : Set
    P : S → Set

open Cont

⟦_⟧ : Cont → Set → Set
⟦ S , P ⟧ X = Σ S λ s → P s → X

-- Every container is strictly positive
tosp : Cont → SPos
tosp C .F = ⟦ C ⟧
tosp C .mon f (s , t) = s , λ p → f (t p)
tosp C .Supp (s , t) = C .P s
tosp C .mon-Supp f (s , t) p = p
tosp C .necc (s , t) p = t p
tosp C .suff (s , t) = s , λ x → x
{-
tosp C .necc-suff = refl
tosp C .suff-necc p = refl
tosp C .suff-nat f xs = refl
tosp C .necc-nat f xs p = refl
tosp C .mon-∙ xs = refl
tosp C .mon-Supp-∙ = λ xs p → refl
-}

-- A stricly positive functor is isomorphic to a container
module M  (sp : SPos) where

  cont : Cont
  cont = sp .F ⊤ , sp .Supp

  G = ⟦ cont ⟧

  fwd : ∀ {X} → sp .F X → G X
  fwd fx = sp .mon _ fx  , λ p → sp .necc fx (sp .mon-Supp _ fx p)

  bwd : ∀ {X} → G X → sp .F X
  bwd (s , t) = sp .mon t (sp .suff s)

{-
  iso1 : ∀ {X} (xs : sp .F X) → bwd (fwd xs) ≡ xs
  iso1 xs = trans
            (trans (sym (sp .mon-∙ (sp .suff (sp .mon _ xs))))
                   (cong (sp .mon (sp .necc xs)) (sp .suff-nat _ xs)))
                   (sp .necc-suff)

  iso2₁ : ∀ {X} (xs : G X) → (fwd (bwd xs)) .proj₁ ≡ xs .proj₁
  iso2₁ (s , t) = trans (sp .mon-∙ (sp .suff s)) (sp .necc-suff)


  iso2₂ : ∀ {X} (xs : G X) {p : _} →
            (fwd (bwd xs)) .proj₂ p ≡ xs .proj₂ (subst (sp .Supp) (iso2₁ xs) p)
  iso2₂ (s , t) {p} = trans (sp .necc-nat  t (sp .suff s) _)
                  (cong t (trans
                          (cong (sp .necc (sp .suff s)) (sp .mon-Supp-∙ (sp .suff s) _))
                                (trans (sp .suff-necc _)
                                       (sym (subst-trans ((sp .mon-∙ (sp .suff s)))
                                                         (sp .necc-suff) p) ))))
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
