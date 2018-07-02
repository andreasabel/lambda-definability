{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

module StrictlyPos where

open import Library

subst-trans : ∀ {A : Set}{P : A → Set} {x y z : A} →
                (p : x ≡ y) → (q : y ≡ z) → (xs : P x) →
                  subst P (trans p q) xs ≡ subst P q (subst P p xs)
subst-trans refl refl xs = refl

-- _S_trictly _P_ositive functors have a well-behaved support

Set^_ : (I : Set) → Set₁
Set^ I = I → Set

_→̇_ : {I : Set} (A B : I → Set) → Set
A →̇ B = ∀{i} (u : A i) → B i

record SPos (I : Set) : Set₁ where
  field
    F    : (ρ : I → Set) → Set
    mon  : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') (x : F ρ) → F ρ'

    Supp : ∀{ρ} (x : F ρ) (i : I) → Set

    mon-Supp : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') (x : F ρ) → Supp (mon ρ→ρ' x) →̇ Supp x

    necc : ∀{ρ} (x : F ρ) → Supp x →̇ ρ
    suff : ∀{ρ} (x : F ρ) → F (Supp x)


{-
    -- laws
    mon-∙ : ∀ {x y z} {g : y → z} {f : x → y} →
            ∀ xs → mon g (mon f xs) ≡ mon (g ∘ f) xs


    mon-Supp-∙ : ∀ {x y z} {g : y → z} {f : x → y} →
                 ∀ xs → (p : Supp (mon g (mon f xs)))
                 → mon-Supp f xs (mon-Supp g (mon f xs) p)
                 ≡ mon-Supp (g ∘ f) xs (subst Supp (mon-∙ xs) p)


    necc-nat : ∀{ρ ρ' : Set} → (f : ρ → ρ') → ∀ (xs : F ρ) (p : Supp (mon f xs))
               → necc (mon f xs) p ≡ f (necc xs (mon-Supp f xs p))

    suff-nat : ∀{ρ ρ'} → (f : ρ → ρ') → ∀ (xs : F ρ)
               → mon (mon-Supp f xs) (suff (mon f xs)) ≡ suff xs


    necc-suff : ∀ {ρ} {x : F ρ} →  mon (necc x) (suff x) ≡ x

    suff-necc : ∀ {ρ} {x : F ρ} (p : Supp _)
                → necc (suff x) (mon-Supp (necc x) (suff x) p)
                ≡ subst Supp necc-suff p
-}
open SPos

-- Constructions on SPos

SP = SPos ∘ Fin

-- Variable

δ : ∀{n} (i j : Fin n) → Set
δ i j = True (i ≟ j)

δ-diag : ∀{n} (i : Fin n) → δ i i ≡ ⊤
δ-diag zero = refl
δ-diag (suc i) with i ≟ i
δ-diag (suc i) | yes p = refl
δ-diag (suc i) | no ¬p = case ¬p refl of λ()

-- {-# REWRITE δ-diag #-}  -- illegal

open module DecFinRefl {n} = DecRefl {A = Fin n} _≟_
{-# REWRITE ≟-refl #-}

-- Type variables (projections)

-- Var could be generalized to decidable I

Var : ∀{n} (i : Fin n) → SP n
Var i .F ρ = ρ i
Var i .mon ρ→ρ' x = ρ→ρ' x
Var i .Supp _ j = δ i j
Var i .mon-Supp ρ→ρ' _ {j} u with i ≟ j
Var i .mon-Supp ρ→ρ' _ {j} _  | yes _ = _
Var i .mon-Supp ρ→ρ' _ {j} () | no _
Var i .necc x {j} u with i ≟ j
Var i .necc x {.i} _ | yes refl = x
Var i .necc x {j} () | no _
Var i .suff = _ -- rewrite δ-diag i = _

-- Constant types have empty support

Const : ∀ (A : Set) {I} → SPos I
Const A .F _ = A
Const A .mon _ = id
Const A .Supp _ _ = ⊥
Const A .mon-Supp _ _ ()
Const A .necc _ ()
Const A .suff = id

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
Fun A B .Supp f i                = ∃ λ (a : A) → B .Supp (f a) i
Fun A B .mon-Supp ρ→ρ' f (a , u) = a , B .mon-Supp ρ→ρ' (f a) u
Fun A B .necc f (a , u)          = B .necc (f a) u
Fun A B .suff f a                = B .mon (a ,_) (B .suff (f a))

Prod : ∀{I} (A B : SPos I) → SPos I
Prod A B .F ρ                            = A .F ρ × B .F ρ
Prod A B .mon ρ→ρ' (a , b)               = A .mon ρ→ρ' a , B .mon ρ→ρ' b
Prod A B .Supp (a , b) i                 = A .Supp a i ⊎ B .Supp b i
Prod A B .mon-Supp ρ→ρ' (a , b) (inj₁ u) = inj₁ (A .mon-Supp ρ→ρ' a u)
Prod A B .mon-Supp ρ→ρ' (a , b) (inj₂ u) = inj₂ (B .mon-Supp ρ→ρ' b u)
Prod A B .necc (a , b) (inj₁ u)          = A .necc a u
Prod A B .necc (a , b) (inj₂ u)          = B .necc b u
Prod A B .suff (a , b)                   = A .mon inj₁ (A .suff a) , B .mon inj₂ (B .suff b)

Sum : ∀{I} (A B : SPos I) → SPos I
Sum A B .F ρ                      = A .F ρ ⊎ B .F ρ
Sum A B .mon ρ→ρ' (inj₁ a)        = inj₁ (A .mon ρ→ρ' a)
Sum A B .mon ρ→ρ' (inj₂ b)        = inj₂ (B .mon ρ→ρ' b)
Sum A B .Supp (inj₁ a) i          = A .Supp a i
Sum A B .Supp (inj₂ b) i          = B .Supp b i
Sum A B .mon-Supp ρ→ρ' (inj₁ a) u = A .mon-Supp ρ→ρ' a u
Sum A B .mon-Supp ρ→ρ' (inj₂ b) u = B .mon-Supp ρ→ρ' b u
Sum A B .necc (inj₁ a) u          = A .necc a u
Sum A B .necc (inj₂ b) u          = B .necc b u
Sum A B .suff (inj₁ a)            = inj₁ (A .suff a)
Sum A B .suff (inj₂ b)            = inj₂ (B .suff b)

ext : ∀{ℓ} {A : Set ℓ} {n} (ρ : Fin n → A) (x : A) (i : Fin (suc n)) → A
ext ρ x zero = x
ext ρ x (suc i) = ρ i

ext-⊤-mon : ∀{n}{ρ ρ' : Fin n → Set} (ρ→ρ' : ρ →̇ ρ') → ext ρ ⊤ →̇ ext ρ' ⊤
ext-⊤-mon ρ→ρ' {zero} = _
ext-⊤-mon ρ→ρ' {suc i} = ρ→ρ'

Mu : ∀{n} (A : SP (suc n)) → SP n
Mu A .F ρ  = 𝕎 (A .F (ext ρ ⊤)) λ x → A .Supp x zero
Mu A .mon {ρ}{ρ'} ρ→ρ' = 𝕎-map (A .mon ρ⊤→ρ'⊤) λ x → A .mon-Supp (λ{i} → ext-⊤-mon ρ→ρ' {i}) x
  where
  ρ⊤→ρ'⊤ : ext ρ ⊤ →̇ ext ρ' ⊤
  ρ⊤→ρ'⊤ {i} = ext-⊤-mon ρ→ρ' {i}
Mu A .Supp w i = EF𝕎 (λ x → A .Supp x (suc i)) w
Mu A .mon-Supp ρ→ρ' x u = {!!}
Mu A .necc (sup x f) (here p)    = A .necc x p
Mu A .necc (sup x f) (there i u) = Mu A .necc (f i) u
Mu A .suff (sup x f) = sup {!!} {!!}

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
