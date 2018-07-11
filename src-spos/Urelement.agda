{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

module Urelement where

open import Library

-- Set-based functors

record SBas (I : Set) : Set₁ where
  field
    -- I-ary functor
    F    : (ρ : I → Set) → Set
    mon  : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') (x : F ρ) → F ρ'

    -- The support relation (urelements).
    U    : ∀{ρ} (x : F ρ) (i : I) (y : ρ i) → Set

  Supp : ∀{ρ} (x : F ρ) (i : I) → Set
  Supp {ρ} x i = ∃ λ (y : ρ i) → U x i y

  necc : ∀{ρ} (x : F ρ) → Supp x →̇ ρ
  necc x {i} = proj₁

  field
    suff : ∀{ρ} (x : F ρ) → F (Supp x)

    mon-U : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') {x : F ρ} {i : I} {y : ρ i} (u : U x i y) → U (mon ρ→ρ' x) i (ρ→ρ' y)

  mon-Supp : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') (x : F ρ) → Supp x →̇ Supp (mon ρ→ρ' x)
  mon-Supp ρ→ρ' x = ρ→ρ' ×̇ mon-U ρ→ρ'

  anti-Supp : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') (x : F ρ) → Supp (mon ρ→ρ' x) →̇ Supp x
  anti-Supp ρ→ρ' x {i} s = {!proj₁ s!}

  supp-suff : ∀{ρ} (x : F ρ) → Supp (suff x) →̇ Supp x
  supp-suff x = proj₁

  -- Laws
  field
    mon-id : ∀{ρ} x → mon {ρ} id x ≡ x
    mon-comp : ∀ {ρ₁ ρ₂ ρ₃} {ρ₂→ρ₃ : ρ₂ →̇  ρ₃} {ρ₁→ρ₂ : ρ₁ →̇  ρ₂} →
            ∀ x → mon {ρ₂} ρ₂→ρ₃ (mon ρ₁→ρ₂ x) ≡ mon (ρ₂→ρ₃ ∘ ρ₁→ρ₂) x

    necc-suff : ∀ {ρ} (x : F ρ) →  mon (necc x) (suff x) ≡ x

  mon-cong : ∀{ρ ρ'} {f f' : ρ →̇  ρ'} (x : F ρ)
      → (eq : ∀{i} y → f (necc x {i} y) ≡ f' (necc x {i} y))
      → mon f x ≡ mon f' x
  mon-cong {ρ} {ρ'} {f} {f'} x eq = begin
    mon f x                        ≡⟨ cong (mon f) (sym (necc-suff x)) ⟩
    mon f (mon (necc x) (suff x))  ≡⟨ mon-comp (suff x) ⟩
    mon (f ∘ necc x) (suff x)      ≡⟨ cong {A = ∀ {i} u → ρ' i} (λ g → mon g (suff x)) (funExtH (funExt eq))  ⟩
    mon (f' ∘ necc x) (suff x)     ≡⟨ sym (mon-comp (suff x)) ⟩
    mon f' (mon (necc x) (suff x)) ≡⟨ cong (mon f') (necc-suff x) ⟩
    mon f' x  ∎
    where open ≡-Reasoning

open SBas
SB = SBas ∘ Fin

Var : ∀{n} (i : Fin n) → SB n
Var i .F ρ         = ρ i
Var i .mon ρ→ρ' x  = ρ→ρ' x
Var i .U x j y     = δ i j
Var i .suff x      = x , _
Var i .mon-U ρ→ρ'  = id
Var i .mon-id x    = refl
Var i .mon-comp x  = refl
Var i .necc-suff x = refl

Const : ∀ (A : Set) {I} → SBas I
Const A .F _         = A
Const A .mon _       = id
Const A .U _ _ _     = ⊥
Const A .suff        = id
Const A .mon-U _     = id
Const A .mon-id _    = refl
Const A .mon-comp x  = refl
Const A .necc-suff x = refl

Empty = Const ⊥
Unit  = Const ⊤

Fun : ∀ (A : Set) {I} (B : SBas I) → SBas I
Fun A B .F ρ                = A → B .F ρ
Fun A B .mon ρ→ρ' f a       = B .mon ρ→ρ' (f a)
Fun A B .U f i y            = ∃ λ (a : A) → B .U (f a) i y
Fun A B .mon-U ρ→ρ' (a , u) = a , B .mon-U ρ→ρ' u
Fun A B .suff f a           = B .mon (id ×̇ (a ,_)) (B .suff (f a))
Fun A B .mon-id f           = funExt λ a → B .mon-id (f a)
Fun A B .mon-comp f         = funExt λ a → B .mon-comp (f a)
Fun A B .necc-suff f        = funExt λ a →
  begin
  -- B .mon (necc (Fun A B) f) (B .mon (id ×̇ (a ,_)) (B .suff (f a)))  ≡⟨⟩

  B .mon proj₁ (B .mon (id ×̇ (a ,_)) (B .suff (f a))) ≡⟨ B .mon-comp (B .suff (f a)) ⟩

  -- B .mon (necc B (f a)) (B .suff (f a))            ≡⟨⟩

  B .mon proj₁ (B .suff (f a))                        ≡⟨ B .necc-suff (f a) ⟩

  f a                                                 ∎ where open ≡-Reasoning -- {!B .necc-suff!}

Prod : ∀{I} (A B : SBas I) → SBas I
Prod A B .F ρ               = A .F ρ × B .F ρ
Prod A B .mon ρ→ρ' (a , b)  = A .mon ρ→ρ' a , B .mon ρ→ρ' b
Prod A B .U (a , b) i y     = A .U a i y ⊎ B .U b i y
Prod A B .mon-U ρ→ρ'        = A .mon-U ρ→ρ' +̇ B .mon-U ρ→ρ'
Prod A B .suff (a , b)      = A .mon (id ×̇ inj₁) (A .suff a) , B .mon (id ×̇ inj₂) (B .suff b)
Prod A B .mon-id (a , b)    = cong₂ _,_ (A .mon-id a) (B .mon-id b)
Prod A B .mon-comp (a , b)  = cong₂ _,_ (A .mon-comp a) (B .mon-comp b)
Prod A B .necc-suff (a , b) = cong₂ _,_
  (trans (A .mon-comp (A .suff a)) (A .necc-suff a))
  (trans (B .mon-comp (B .suff b)) (B .necc-suff b))

Sum : ∀{I} (A B : SBas I) → SBas I
Sum A B .F ρ                 = A .F ρ ⊎ B .F ρ
Sum A B .mon ρ→ρ'            = A .mon ρ→ρ' +̇ B .mon ρ→ρ'
Sum A B .U {ρ}               = [ A .U {ρ} , B .U {ρ} ]
Sum A B .mon-U ρ→ρ' {inj₁ a} = A .mon-U ρ→ρ'
Sum A B .mon-U ρ→ρ' {inj₂ b} = B .mon-U ρ→ρ'
Sum A B .suff (inj₁ a)       = inj₁ (A .suff a)
Sum A B .suff (inj₂ b)       = inj₂ (B .suff b)
Sum A B .mon-id (inj₁ a)     = cong inj₁ (A .mon-id a)
Sum A B .mon-id (inj₂ b)     = cong inj₂ (B .mon-id b)
Sum A B .mon-comp (inj₁ a)   = cong inj₁ (A .mon-comp a)
Sum A B .mon-comp (inj₂ b)   = cong inj₂ (B .mon-comp b)
Sum A B .necc-suff (inj₁ a)  = cong inj₁ (A .necc-suff a)
Sum A B .necc-suff (inj₂ b)  = cong inj₂ (B .necc-suff b)

ext : ∀{ℓ} {A : Set ℓ} {n} (ρ : Fin n → A) (x : A) (i : Fin (suc n)) → A
ext ρ x zero = x
ext ρ x (suc i) = ρ i

ext-forget : ∀{n ρ A} i → ext {n = n} ρ A i → ext ρ ⊤ i
ext-forget zero    = _
ext-forget (suc _) = id

ext-⊤-mon : ∀{n}{ρ ρ' : Fin n → Set} (ρ→ρ' : ρ →̇ ρ') → ext ρ ⊤ →̇ ext ρ' ⊤
ext-⊤-mon ρ→ρ' {zero} = _
ext-⊤-mon ρ→ρ' {suc i} = ρ→ρ'

Mu : ∀{n} (A : SB (suc n)) → SB n
Mu A .F ρ  = 𝕎 (A .F (ext ρ ⊤)) λ x → A .U x zero _
Mu A .mon {ρ}{ρ'} ρ→ρ' = 𝕎-map (A .mon λ{i} → ext-⊤-mon ρ→ρ' {i})
                                (λ x u → {!A .mon-U (λ{i} → ext-⊤-mon ρ→ρ' {i}) {x}!})
Mu A .U w i y               = EF𝕎 (λ x → A .U x (suc i) y) w
Mu A .mon-U {ρ} ρ→ρ' x = {! EF𝕎-map
  (A .mon (λ{j} → ext-⊤-mon ρ→ρ' {j}))
  (λ y → A .mon-U (λ {j} → ext-⊤-mon ρ→ρ' {j}) {y})
  (λ y → A .mon-U (λ {j} → ext-⊤-mon ρ→ρ' {j}) {y})
  ? !}
Mu A .suff x = 𝕎-map {!!} {!!} x
Mu A .mon-id = {!!}
Mu A .mon-comp = {!!}
Mu A .necc-suff = {!!}
