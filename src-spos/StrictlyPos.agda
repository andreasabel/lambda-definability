{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

module StrictlyPos where

open import Library
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as ListProp

subst-trans : ∀ {A : Set}{P : A → Set} {x y z : A} →
                (p : x ≡ y) → (q : y ≡ z) → (xs : P x) →
                  subst P (trans p q) xs ≡ subst P q (subst P p xs)
subst-trans refl refl xs = refl

subst-∃ : {A A' : Set}{B : A → A' → Set} {a : A} {x y : A'} →
          (eq : x ≡ y) (u : B a x) → subst (λ x → ∃ λ a → B a x) eq (a , u) ≡ (a , subst (λ x → B a x) eq u)
subst-∃ refl u = refl

-- _S_trictly _P_ositive functors have a well-behaved support

record SPos (I : Set) : Set₁ where
  field
    -- I-ary functor
    F    : (ρ : I → Set) → Set
    mon  : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') (x : F ρ) → F ρ'

    -- Supp is, in terms of Container terminology, the set of content positions.
    Supp : ∀{ρ} (x : F ρ) (i : I) → Set

    -- necc is the map from positions to content.
    necc : ∀{ρ} (x : F ρ) → Supp x →̇ ρ

    -- suff is a "numbering" of the positions in a tree.
    suff : ∀{ρ} (x : F ρ) → F (Supp x)

    anti-Supp : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') (x : F ρ) → Supp (mon ρ→ρ' x) →̇ Supp x
    supp-suff : ∀{ρ} (x : F ρ) → Supp (suff x) →̇ Supp x

    -- anti-Supp and supp-suff can be merged into a single law anti-Supp-suff
    anti-Supp-suff : ∀{ρ ρ'} (x : F ρ) (supp→ρ' : Supp x →̇ ρ') → Supp (mon supp→ρ' (suff x)) →̇ Supp x


    -- Laws

    mon-id : ∀{ρ} x → mon {ρ} id x ≡ x
    mon-comp : ∀ {ρ₁ ρ₂ ρ₃} {ρ₂→ρ₃ : ρ₂ →̇  ρ₃} {ρ₁→ρ₂ : ρ₁ →̇  ρ₂} →
            ∀ x → mon {ρ₂} ρ₂→ρ₃ (mon ρ₁→ρ₂ x) ≡ mon (ρ₂→ρ₃ ∘ ρ₁→ρ₂) x

    -- If  f  and  f'  coincide on the support of  x
    -- then  mon f  and  mon f'  coincide on  x.

    -- (Redundant, see def-mon-cong below.)

    mon-cong : ∀{ρ ρ'} {f f' : ρ →̇  ρ'} (x : F ρ)
      → (eq : ∀{i} y → f (necc x {i} y) ≡ f' (necc x {i} y))
      → mon f x ≡ mon f' x

    anti-Supp-id : ∀{ρ} x {i} p → anti-Supp {ρ} id x {i} p ≡ subst (λ x → Supp x i) (mon-id {ρ} x) p

    -- anti-Supp-id : ∀{ρ} (x : F ρ) →
    --   (λ{i} → anti-Supp {ρ} id x {i}) ≡  λ{i} → subst (λ f → Supp (f x) i) (mon-id {ρ})

    necc-suff : ∀ {ρ} (x : F ρ) →  mon (necc x) (suff x) ≡ x

    suff-nat : ∀{ρ ρ'} → (f : ρ →̇  ρ') → ∀ (x : F ρ)
               → mon (anti-Supp f x) (suff (mon f x)) ≡ suff x

    necc-nat : ∀{ρ ρ'} → (f : ρ →̇  ρ') → ∀ (x : F ρ) {i} → (p : Supp (mon f x) i)
               → necc (mon f x) p ≡ f (necc x (anti-Supp f x p))

{-

    anti-Supp-comp : ∀ {x y z} {g : y → z} {f : x → y} →
                 ∀ xs → (p : Supp (mon g (mon f xs)))
                 → anti-Supp f xs (anti-Supp g (mon f xs) p)
                 ≡ anti-Supp (g ∘ f) xs (subst Supp (mon-comp xs) p)




    suff-necc : ∀ {ρ} {x : F ρ} (p : Supp _)
                → necc (suff x) (anti-Supp (necc x) (suff x) p)
                ≡ subst Supp necc-suff p
-}
  def-anti-Supp-suff : ∀{ρ ρ'} (x : F ρ) (supp→ρ' : Supp x →̇ ρ') → Supp (mon supp→ρ' (suff x)) →̇ Supp x
  def-anti-Supp-suff ρ→ρ' x p = supp-suff ρ→ρ' (anti-Supp x (suff ρ→ρ') p)

  def-anti-Supp : ∀{ρ ρ'} (ρ→ρ' : ρ →̇ ρ') (x : F ρ) → Supp (mon ρ→ρ' x) →̇ Supp x
  def-anti-Supp ρ→ρ' x {i} u = anti-Supp-suff x (ρ→ρ' ∘ necc x) u'
    where
    prf : mon ρ→ρ' x ≡ mon (ρ→ρ' ∘ necc x) (suff x)
    prf = begin
      mon ρ→ρ' x                        ≡⟨ cong (mon ρ→ρ') (sym (necc-suff x)) ⟩
      mon ρ→ρ' (mon (necc x) (suff x))  ≡⟨ mon-comp (suff x) ⟩
      mon (ρ→ρ' ∘ necc x) (suff x)      ∎ where open ≡-Reasoning
    u' : Supp (mon (ρ→ρ' ∘ necc x) (suff x)) i
    u' = subst (λ z → Supp z i) prf u

  def-anti-Supp-id : ∀{ρ} x {i} p → def-anti-Supp {ρ} id x {i} p ≡ subst (λ x → Supp x i) (mon-id {ρ} x) p
  def-anti-Supp-id {ρ} x {i} p = {!!} -- rewrite mon-id x = {!!}

  mon-id! : ∀{ρ} → mon {ρ} id ≡ id
  mon-id! = funExt λ x → mon-id x

  anti-Supp-id! : ∀{ρ} (x : F ρ) →
    (λ{i} → anti-Supp {ρ} id x {i}) ≡  λ{i} → subst (λ f → Supp (f x) i) (mon-id! {ρ})
  anti-Supp-id! x = funExtH λ{i} → funExt λ p →
    begin
      anti-Supp id x p                       ≡⟨ anti-Supp-id x p ⟩
      subst (λ y → Supp y i) (mon-id x) p   ≡⟨ subst-ext (λ v → Supp v i) mon-id p ⟩
      subst (λ f → Supp (f x) i) mon-id! p  ∎ where open ≡-Reasoning


  -- If  f  and  f'  coincide on the support of  x
  -- then  mon f  and  mon f'  coincide on  x.

   -- This is a consequence of necc-suff (and mon-comp).

  def-mon-cong : ∀{ρ ρ'} {f f' : ρ →̇  ρ'} (x : F ρ)
      → (eq : ∀{i} y → f (necc x {i} y) ≡ f' (necc x {i} y))
      → mon f x ≡ mon f' x
  def-mon-cong {ρ} {ρ'} {f} {f'} x eq = begin
    mon f x                        ≡⟨ cong (mon f) (sym (necc-suff x)) ⟩
    mon f (mon (necc x) (suff x))  ≡⟨ mon-comp (suff x) ⟩
    mon (f ∘ necc x) (suff x)      ≡⟨ cong {A = ∀ {i} u → ρ' i} (λ g → mon g (suff x)) (funExtH (funExt eq))  ⟩
    mon (f' ∘ necc x) (suff x)     ≡⟨ sym (mon-comp (suff x)) ⟩
    mon f' (mon (necc x) (suff x)) ≡⟨ cong (mon f') (necc-suff x) ⟩
    mon f' x  ∎
    where open ≡-Reasoning

open SPos

-- Examples:

-- Lists are a unary sp functor

length-tabulate : ∀ n {a} {A : Set a} {f : Fin n → A} → List.foldr (λ _ → suc) 0 (List.tabulate f) ≡ n
length-tabulate zero = refl
length-tabulate (suc n) = cong suc (length-tabulate n)

{-# REWRITE length-tabulate #-}
-- {-# REWRITE ListProp.length-map #-}  -- not a legal rewrite rule since length is defined in terms of foldr

foldr-map : ∀{a b c}{A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (cons : B → C → C) (nil : C) (xs : List A)
  → List.foldr cons nil (List.map f xs) ≡ List.foldr (λ a → cons (f a)) nil xs
foldr-map f cons nil []       = refl
foldr-map f cons nil (x ∷ xs) = cong (cons (f x)) (foldr-map f cons nil xs)

{-# REWRITE foldr-map #-}

incr : ∀ n {m} (i : Fin m) → Fin (n + m)
incr zero    i = i
incr (suc n) i = suc (incr n i)


fromℕ' : (n {m} : ℕ) → Fin (n + suc m)
fromℕ' zero        = zero
fromℕ' (suc n) {m} = suc (fromℕ' n {m})

incr-zero : ∀ n {m} → incr n (zero {m}) ≡ fromℕ' n
incr-zero zero = refl
incr-zero (suc n) = cong suc (incr-zero n)

{-# REWRITE incr-zero #-}

{-# REWRITE ListProp.foldr-++ #-}

foldr-suc-length : ∀{a}{A : Set a} (xs {ys} : List A)
  → List.foldr (λ _ → suc) (List.length ys) xs ≡ List.length xs + List.length ys
foldr-suc-length [] = refl
foldr-suc-length (x ∷ xs) {ys} = cong suc (foldr-suc-length xs {ys})

{-# REWRITE foldr-suc-length #-}

map-lookup-tabulate : ∀{a} {A : Set a} (xs ys : List A)
  → List.map (List.lookup (xs List.++ ys)) (List.tabulate (incr (List.length xs))) ≡ ys
map-lookup-tabulate xs [] = refl
map-lookup-tabulate xs (y ∷ ys) = {!cong₂ List._∷_ ? ?!}

-- {-# REWRITE map-lookup-tabulate #-}

map-lookup-allFin : ∀{a}{A : Set a} (xs : List A)
  → List.map (List.lookup xs) (List.allFin (List.length xs)) ≡ xs
map-lookup-allFin [] = refl
map-lookup-allFin (x ∷ xs) = cong (x ∷_) {!!}

{-# REWRITE map-lookup-allFin #-}

List-SP : SPos ⊤
List-SP .F X = List (X _)
List-SP .mon f = List.map f
List-SP .Supp {ρ} xs _ = Fin (List.length xs) -- ρ _
List-SP .anti-Supp f xs u = u -- subst Fin (ListProp.length-map f xs) u -- id
List-SP .necc xs {i} = {! List.lookup xs !}
-- List-SP .necc xs u = List.lookup xs u  -- FAILS rewriting
List-SP .suff xs = List.allFin (List.length xs)
List-SP .supp-suff x u = u -- id
List-SP .anti-Supp-suff xs supp→ρ' u = u
List-SP .mon-id = ListProp.map-id
List-SP .mon-comp = {!!}
List-SP .mon-cong = {!!}
List-SP .anti-Supp-id = {!!}
List-SP .necc-suff {ρ} xs =  {! refl !}   -- fails on reload!?
List-SP .suff-nat f x = {!!}
List-SP .necc-nat = {!!}

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
Var i .Supp _ j = δ i j
Var i .anti-Supp ρ→ρ' _ = id
Var i .necc x {j} u with i ≟ j
Var i .necc x {.i} _ | yes refl = x
Var i .necc x {j} () | no _
Var i .suff = _ -- rewrite δ-diag i = _
Var i .supp-suff x = id
Var i .anti-Supp-suff x supp→ρ' u = u
Var i .mon-id _ = refl
Var i .mon-comp x = refl
Var i .mon-cong x eq = eq {i} _
Var i .anti-Supp-id {ρ} _ _ = refl
Var i .necc-suff x = refl
Var i .suff-nat = λ f xs → refl
Var i .necc-nat f xs {j} p with i ≟ j
Var i .necc-nat f xs {.i} p | yes refl = refl
Var i .necc-nat f xs {j} () | no ¬p

-- Constant types have empty support

Const : ∀ (A : Set) {I} → SPos I
Const A .F _ = A
Const A .mon _ = id
Const A .Supp _ _ = ⊥
Const A .anti-Supp _ _ = id
Const A .necc _ ()
Const A .suff = id
Const A .supp-suff x = id
Const A .anti-Supp-suff _ _ = id
Const A .mon-id _ = refl
Const A .mon-comp x = refl
Const A .mon-cong x eq = refl
Const A .anti-Supp-id _ _ = refl
Const A .necc-suff x = refl
Const A .suff-nat = λ f xs → refl
Const A .necc-nat f xs ()

Empty = Const ⊥
Unit  = Const ⊤

Fun : ∀ (A : Set) {I} (B : SPos I) → SPos I
Fun A B .F ρ                     = A → B .F ρ
Fun A B .mon ρ→ρ' f a            = B .mon ρ→ρ' (f a)
Fun A B .Supp f i                = ∃ λ (a : A) → B .Supp (f a) i
Fun A B .anti-Supp ρ→ρ' f (a , u) = a , B .anti-Supp ρ→ρ' (f a) u
Fun A B .necc f (a , u)          = B .necc (f a) u
Fun A B .suff f a                = B .mon (a ,_) (B .suff (f a))
Fun A B .supp-suff f (a , u)     = a , B .supp-suff (f a) (B .anti-Supp (a ,_) (B .suff (f a)) u)
Fun A B .anti-Supp-suff f supp→ρ' (a , u) = a , B .anti-Supp-suff (f a) (λ{i} u → supp→ρ' (a , u)) (subst (λ x → B .Supp x _) (B .mon-comp (B .suff (f a))) u)
Fun A B .mon-id f                = funExt λ a → B .mon-id (f a)
Fun A B .mon-comp f              = funExt λ a → B .mon-comp (f a)
Fun A B .mon-cong f eq           = funExt λ a → B .mon-cong (f a) (λ{i} y → eq {i} (a , y))
Fun A B .anti-Supp-id {ρ} f {i} (a , u) =
  trans (cong (_,_ a) (trans (B .anti-Supp-id (f a) u) (sym (funExt-β (λ a₁ → B .mon-id (f a₁)) a (λ v → B .Supp v i) u))))
        (sym (subst-∃ {B = λ v v₁ → B .Supp (v₁ v) i} ((funExt (λ a₁ → B .mon-id (f a₁)))) u))
  -- does not rewrite
  -- rewrite (subst-∃ {B = λ v v₁ → B .Supp (v₁ v) i} ((funExt (λ a₁ → B .mon-id (f a₁)))) u)
  --   = {!!}
Fun A B .necc-suff f = funExt λ a →
  begin
  B .mon (Fun A B .necc f) (B .mon (a ,_) (B .suff (f a)))  ≡⟨ B .mon-comp (B .suff (f a)) ⟩
  B .mon (Fun A B .necc f ∘ (a ,_)) (B .suff (f a))         ≡⟨⟩
  B .mon (B .necc (f a)) (B .suff (f a))                    ≡⟨ B .necc-suff (f a) ⟩
  f a                                                       ∎ where open ≡-Reasoning -- {!B .necc-suff!}
Fun A B .necc-nat f xs p = B .necc-nat f (xs (p .proj₁)) (p .proj₂)
Fun A B .suff-nat f xs = funExt (λ x → trans (trans (B .mon-comp (B .suff (B .mon f (xs x))))
                                ((sym ((B .mon-comp (B .suff (B .mon f (xs x))))))))
                                (cong (B .mon (λ {_} section → x , section)) (B .suff-nat f (xs x))))

Prod : ∀{I} (A B : SPos I) → SPos I
Prod A B .F ρ                            = A .F ρ × B .F ρ
Prod A B .mon ρ→ρ' (a , b)               = A .mon ρ→ρ' a , B .mon ρ→ρ' b
Prod A B .Supp (a , b) i                 = A .Supp a i ⊎ B .Supp b i
Prod A B .anti-Supp ρ→ρ' (a , b)          = A .anti-Supp ρ→ρ' a +̇ B .anti-Supp ρ→ρ' b
Prod A B .necc (a , b)                   = [ A .necc a , B .necc b ]
Prod A B .suff (a , b)                   = A .mon inj₁ (A .suff a) , B .mon inj₂ (B .suff b)
Prod A B .supp-suff (a , b)              = (A .supp-suff a ∘ A .anti-Supp inj₁ (A .suff a))
                                         +̇ (B .supp-suff b ∘ B .anti-Supp inj₂ (B .suff b))
Prod A B .anti-Supp-suff (a , b) supp→ρ' (inj₁ u) = inj₁ (A .anti-Supp-suff a (λ{i} u' → supp→ρ' (inj₁ u')) (subst (λ x → A .Supp x _) (A .mon-comp (A .suff a)) u))
Prod A B .anti-Supp-suff (a , b) supp→ρ' (inj₂ u) = inj₂ (B .anti-Supp-suff b (λ{i} u' → supp→ρ' (inj₂ u')) (subst (λ x → B .Supp x _) (B .mon-comp (B .suff b)) u))
Prod A B .mon-id (a , b)                 = cong₂ _,_ (A .mon-id a) (B .mon-id b)
Prod A B .mon-comp (a , b)               = cong₂ _,_ (A .mon-comp a) (B .mon-comp b)
Prod A B .mon-cong (a , b) eq            = cong₂ _,_ (A .mon-cong a (eq ∘ inj₁)) (B .mon-cong b (eq ∘ inj₂))
Prod {I} A B .anti-Supp-id {ρ} (a , b) (inj₁ l)
  rewrite A .anti-Supp-id a l | A .mon-id a | B .mon-id b = refl
Prod {I} A B .anti-Supp-id {ρ} (a , b) (inj₂ r)
  rewrite B .anti-Supp-id b r | A .mon-id a | B .mon-id b = refl
Prod A B .necc-suff (a , b) = cong₂ _,_
  (trans (A .mon-comp (A .suff a)) (A .necc-suff a))
  (trans (B .mon-comp (B .suff b)) (B .necc-suff b))
Prod A B .suff-nat f xs = cong₂ _,_ (trans (A .mon-comp (A .suff _)) (trans (sym (A .mon-comp {ρ₂→ρ₃ = inj₁} (A .suff _))) (cong (A .mon inj₁) (A .suff-nat f (xs .proj₁)))))
                                    (trans (B .mon-comp (B .suff _)) (trans (sym (B .mon-comp {ρ₂→ρ₃ = inj₂} (B .suff _))) (cong (B .mon inj₂) (B .suff-nat f (xs .proj₂)))))
Prod A B .necc-nat f xs (inj₁ x) = A .necc-nat f (xs .proj₁) x
Prod A B .necc-nat f xs (inj₂ y) = B .necc-nat f (xs .proj₂) y

{-# TERMINATING #-}
Sum : ∀{I} (A B : SPos I) → SPos I
Sum A B .F ρ                      = A .F ρ ⊎ B .F ρ
Sum A B .mon ρ→ρ'                 = A .mon ρ→ρ' +̇ B .mon ρ→ρ'
Sum A B .Supp {ρ}                 = [ A .Supp {ρ} , B .Supp {ρ} ]
Sum A B .anti-Supp ρ→ρ'            = [ A .anti-Supp ρ→ρ' , B .anti-Supp ρ→ρ' ]
Sum A B .necc {ρ}                 = [ A .necc {ρ} , B .necc {ρ} ]
-- NOT POSSIBLE BECAUSE OF DEPENDENCY: Sum A B .suff {ρ} = A .suff {ρ} +̇ B .suff {ρ}
Sum A B .suff (inj₁ a)            = inj₁ (A .suff a)
Sum A B .suff (inj₂ b)            = inj₂ (B .suff b)
Sum A B .supp-suff (inj₁ a)       = A .supp-suff a
Sum A B .supp-suff (inj₂ b)       = B .supp-suff b
Sum A B .anti-Supp-suff (inj₁ a) supp→ρ' u = A .anti-Supp-suff a supp→ρ' u
Sum A B .anti-Supp-suff (inj₂ b) supp→ρ' u = B .anti-Supp-suff b supp→ρ' u
Sum A B .mon-id (inj₁ a) = cong inj₁ (A .mon-id a)
Sum A B .mon-id (inj₂ b) = cong inj₂ (B .mon-id b)
Sum A B .mon-comp (inj₁ a) = cong inj₁ (A .mon-comp a)
Sum A B .mon-comp (inj₂ b) = cong inj₂ (B .mon-comp b)
Sum A B .mon-cong (inj₁ a) eq = cong inj₁ (A .mon-cong a eq)
Sum A B .mon-cong (inj₂ b) eq = cong inj₂ (B .mon-cong b eq)
Sum A B .anti-Supp-id {ρ} (inj₁ a) p rewrite A .anti-Supp-id a p | A .mon-id a = refl
Sum A B .anti-Supp-id {ρ} (inj₂ b) p rewrite B .anti-Supp-id b p | B .mon-id b = refl
Sum A B .necc-suff (inj₁ a) = cong inj₁ (A .necc-suff a)
Sum A B .necc-suff (inj₂ b) = cong inj₂ (B .necc-suff b)
Sum A B .suff-nat f (inj₁ x) = cong inj₁ (A .suff-nat f x)
Sum A B .suff-nat f (inj₂ y) = cong inj₂ (B .suff-nat f y)
Sum A B .necc-nat f (inj₁ x) p = A .necc-nat f x p
Sum A B .necc-nat f (inj₂ y) p = B .necc-nat f y p

ext : ∀{ℓ} {A : Set ℓ} {n} (ρ : Fin n → A) (x : A) (i : Fin (suc n)) → A
ext ρ x zero = x
ext ρ x (suc i) = ρ i

ext-forget : ∀{n ρ A} i → ext {n = n} ρ A i → ext ρ ⊤ i
ext-forget zero    = _
ext-forget (suc _) = id

ext-⊤-mon' : ∀{n}{ρ ρ' : Fin n → Set} (ρ→ρ' : ρ →̇ ρ') {X : Set} → ext ρ X →̇ ext ρ' ⊤
ext-⊤-mon' ρ→ρ' {X} {zero} = _
ext-⊤-mon' ρ→ρ' {X} {suc i} = ρ→ρ'

ext-⊤-mon : ∀{n}{ρ ρ' : Fin n → Set} (ρ→ρ' : ρ →̇ ρ') → ext ρ ⊤ →̇ ext ρ' ⊤
ext-⊤-mon ρ→ρ' {zero} = _
ext-⊤-mon ρ→ρ' {suc i} = ρ→ρ'

-- ext-⊤-mon-id : ∀{n} {ρ : Fin n → Set} → _≡_ {A = ext ρ ⊤ →̇ ext ρ ⊤} (λ{i} → ext-⊤-mon {n} {ρ} id {i}) id
ext-⊤-mon-id : ∀{n} {ρ : Fin n → Set} → (λ{i} → ext-⊤-mon {n} {ρ} id {i}) ≡ id
ext-⊤-mon-id = funExtH λ{ {zero} → refl ; {suc i} → refl }

{-# REWRITE ext-⊤-mon-id #-}

Mu-ζ : ∀{n} (A : SP (suc n)) {ρ}
  → (w : 𝕎 (A .F (ext ρ ⊤)) (λ x → A .Supp x zero))
  → A .Supp (𝕎.head w) →̇ ext (λ i → EF𝕎 (λ x → A .Supp x (suc i)) (𝕎-eta w)) ⊤ --  ext (Mu A .Supp w) ⊤
-- Mu-ζ {n} A {ρ} w = {! ext-⊤-mon here !}
Mu-ζ {n} A {ρ} w {zero}  u = _
Mu-ζ {n} A {ρ} w {suc i} u = here u

Mu+ : ∀{n} (A : SP (suc n)) (X : Set) (ρ : Fin n → Set) → Set
Mu+ A X ρ = 𝕎 (A .F (ext ρ X)) λ x → A .Supp x zero

Mu+map⊤ : ∀{n} (A : SP (suc n)) {ρ ρ'} (ρ→ρ' : ρ →̇ ρ') {X : Set} (x : Mu+ A X ρ) → Mu+ A ⊤ ρ'
Mu+map⊤ {n} A {ρ} {ρ'} ρ→ρ' {X} =
  𝕎.map (A .mon λ{i} → ext-⊤-mon' ρ→ρ' {X} {i})
         (λ x → A .anti-Supp (λ{i} → ext-⊤-mon' ρ→ρ' {X} {i}) x)
-- Mu+map : ∀{n} (A : SP (suc n)) {ρ ρ'} (ρ→ρ' : ρ →̇ ρ') {X Y : Set} (f : X → Y) (x : Mu+ A X ρ) → Mu+ A X ρ'
-- Mu+map {n} A {ρ} {ρ'} ρ→ρ' {X} {Y} f w = {!𝕎-map (A .mon λ{i} → ext-⊤-mon ρ→ρ' {i})
--                                 (λ x → A .anti-Supp (λ{i} → ext-⊤-mon ρ→ρ' {i}) x)!}

{-# TERMINATING #-}
Mu : ∀{n} (A : SP (suc n)) → SP n
Mu A .F ρ  = 𝕎 (A .F (ext ρ ⊤)) λ x → A .Supp x zero
Mu A .mon {ρ}{ρ'} ρ→ρ' = 𝕎.map (A .mon λ{i} → ext-⊤-mon ρ→ρ' {i})
                                (λ x → A .anti-Supp (λ{i} → ext-⊤-mon ρ→ρ' {i}) x)

Mu A .mon-id {ρ} x with A .mon {ext ρ ⊤} id | mon-id! A {ext ρ ⊤} | A .anti-Supp {ext ρ ⊤} id | anti-Supp-id! A {ext ρ ⊤}
Mu A .mon-id {ρ} x | .id | refl | v | p rewrite funExt p = 𝕎-map-id x

Mu A .Supp w i                = EF𝕎 (λ x → A .Supp x (suc i)) w
Mu A .anti-Supp {ρ} ρ→ρ' x {i} = EF𝕎-map
  (A .mon (λ{j} → ext-⊤-mon ρ→ρ' {j}))
  (λ y → A .anti-Supp (λ {j} → ext-⊤-mon ρ→ρ' {j}) y)
  (λ y → A .anti-Supp (λ {j} → ext-⊤-mon ρ→ρ' {j}) y)
  x
Mu A .necc {ρ} x u = let x' , p = 𝕎-lookup x u in A .necc x' p
Mu A .suff {ρ} (sup x f) = sup (A .mon (Mu-ζ A (sup x f)) (A .suff x)) λ p →
  let
    r : 𝕎 (A .F (ext ρ ⊤)) (λ y → A .Supp y zero)
    r = f (A .anti-Supp-suff x (Mu-ζ A (sup x f)) p)
  in
      𝕎.map (A .mon (λ {i} → α p {i}))
        (β p) (Mu A .suff r)
  where

  α : ∀ p
      → ext (Mu A .Supp (f (A .anti-Supp-suff x (Mu-ζ A (sup x f)) p))) ⊤
      →̇ ext (Mu A .Supp (sup x f)) ⊤
  α p {i} = ext-⊤-mon (there (A .anti-Supp-suff x (Mu-ζ A (sup x f)) p)) {i}


  β : ∀ (p : A .Supp (A .mon (Mu-ζ A (sup x f)) (A .suff x)) zero)
        (s : A .F (ext (Mu A .Supp (f (A .anti-Supp-suff x (Mu-ζ A (sup x f)) p))) ⊤))
      → A .Supp (A .mon (λ {i} → α p {i}) s) zero
      → A .Supp s                          zero
  β p s q = A .anti-Supp-suff s _
    (subst (λ s → A .Supp s zero) (A .mon-comp (A .suff s))
      (subst (λ s → A .Supp (A .mon ((λ {i} → α p {i})) s) zero) (sym (A .necc-suff s)) q))
  -- β {p} s q = A .anti-Supp-suff s _ q''
  --   where
  --     q' = subst (λ s → A .Supp (A .mon ((λ {i} → α p i)) s) zero) (sym (A .necc-suff)) q
  --     q'' = subst (λ s → A .Supp s zero) (A .mon-comp (A .suff s)) q'

  -- Inlined for the sake of termination:
  -- x' : A .F (ext (Mu A .Supp (sup x f)) ⊤)
  -- x' = A .mon (Mu-ζ A (sup x f)) (A .suff x)
Mu A .suff-nat = {!!}
Mu A .necc-nat = {!!}
Mu A .supp-suff x u             = {!!}
Mu A .anti-Supp-suff x supp→ρ' u = {!!}
Mu A .mon-comp x                = {!!}
Mu A .mon-cong x eq                = {!!}
Mu A .anti-Supp-id x p           = {!!}
Mu A .necc-suff x               = {!!}

inMu : ∀{n} (A : SP (suc n)) {ρ} (t : A .F (ext ρ (Mu A .F ρ))) → Mu A .F ρ
--  inMu A {ρ} t = {! Mu+map⊤ A (λ{i} → ext-⊤-mon' ? ? {i}) (sup t (A .necc t)) !}
inMu A {ρ} t = sup (A .mon (λ{i} → ext-forget i) t) (A .necc t ∘ A .anti-Supp (λ{i} → ext-forget i) t)

outMu : ∀{n} (A : SP (suc n)) {ρ} (t : Mu A .F ρ) → A .F (ext ρ (Mu A .F ρ))
outMu A {ρ} (sup x f) = A .mon (λ{i} → ψ {i}) (A .suff x)
  module out where
  ψ : A .Supp {ext ρ ⊤} x →̇ ext ρ (Mu A .F ρ)
  ψ {zero} = f
  ψ {suc i} = A .necc x {suc i}

outMu∘inMu : ∀{n} (A : SP (suc n)) {ρ} (t : A .F (ext ρ (Mu A .F ρ))) → outMu A (inMu A t) ≡ t
outMu∘inMu {n} A {ρ} t =
  begin
  A .mon (out.ψ A (A .mon (λ {i} → ext-forget i) t) (λ x → A .necc t (A .anti-Supp (λ {i} → ext-forget i) t x)))
         (A .suff (A .mon (λ {i} → ext-forget i) t))

    ≡⟨ cong (\ (f : A .Supp (A .mon (λ {i} → ext-forget i) t) →̇ ext ρ (𝕎 (A .F (ext ρ ⊤)) (λ x → A .Supp x zero)))
                                                          → A .mon f (A .suff (A .mon (λ {i} → ext-forget i) t)))
                                (funExtH \ { {zero} → refl ; {suc i} → funExt (\ p → A .necc-nat (λ {i₁} → ext-forget i₁) t p) }) ⟩

  A .mon (λ {i} → (A .necc t) ∘ A .anti-Supp (λ {i} → ext-forget i) t)
         (A .suff (A .mon (λ {i} → ext-forget i) t))

    ≡⟨ sym (A .mon-comp (A .suff (A .mon (λ {i} → ext-forget i) t))) ⟩

  A .mon (A .necc t) (A .mon (A .anti-Supp (λ {i} → ext-forget i) t)
         (A .suff (A .mon (λ {i} → ext-forget i) t)))

    ≡⟨ cong (A .mon _) (A .suff-nat ((λ {i} → ext-forget i)) t) ⟩

  A .mon (A .necc t) (A .suff t)

    ≡⟨ A .necc-suff t ⟩

  t ∎ where open ≡-Reasoning

iterMu :  ∀{n} (A : SP (suc n)) {ρ} {C} (s : A .F (ext ρ C) → C) (t : Mu A .F ρ) → C
iterMu A {ρ} {C} s (sup x f) = s (A .mon (λ{i} → ψ {i}) (A .suff x))
  where
  ψ : A .Supp {ext ρ ⊤} x →̇ ext ρ C
  ψ {zero} = iterMu A s ∘ f
  ψ {suc i} = A .necc x {suc i}


Nu-ζ : ∀{n} (A : SP (suc n)) {ρ}
  → (m : 𝕄 (A .F (ext ρ ⊤)) (λ x → A .Supp x zero))
  → A .Supp (m .shape) →̇ ext (λ i → EF𝕄 (λ x → A .Supp x (suc i)) m) ⊤ --  ext (Nu A .Supp m) ⊤
Nu-ζ {n} A {ρ} m {zero}  u = _
Nu-ζ {n} A {ρ} m {suc i} u = here u

Nu : ∀{n} (A : SP (suc n)) → SP n
Nu A .F ρ = 𝕄 (A .F (ext ρ ⊤)) (λ x → A .Supp x zero)
Nu A .mon ρ→ρ' = 𝕄-map (A .mon λ{i} → ext-⊤-mon ρ→ρ' {i}) (λ x → A .anti-Supp (λ{i} → ext-⊤-mon ρ→ρ' {i}) x)
Nu A .Supp  m i = EF𝕄 (λ x → A .Supp x (suc i)) m
Nu A .anti-Supp {ρ} ρ→ρ' x {i} = EF𝕄-map
  (A .mon (λ{j} → ext-⊤-mon ρ→ρ' {j}))
  (λ y → A .anti-Supp (λ {j} → ext-⊤-mon ρ→ρ' {j}) y)
  (λ y → A .anti-Supp (λ {j} → ext-⊤-mon ρ→ρ' {j}) y)
  x
Nu A .necc {ρ} x u = let x' , p = 𝕄-lookup x u in A .necc x' p
Nu A .suff = {!!}
Nu A .supp-suff = {!!}
Nu A .anti-Supp-suff = {!!}
Nu A .mon-id {ρ} x with A .mon {ext ρ ⊤} id | mon-id! A {ext ρ ⊤} | A .anti-Supp {ext ρ ⊤} id | anti-Supp-id! A {ext ρ ⊤}
Nu A .mon-id {ρ} x | .id | refl | v | p rewrite funExt p = 𝕄-map-id x
Nu A .mon-comp = {!!}
Nu A .mon-cong x eq = {!!}
Nu A .anti-Supp-id = {!!}
Nu A .necc-suff = {!!}
Nu A .suff-nat f xs   = {!!}
Nu A .necc-nat f xs p = {!!}

inNu : ∀{n} (A : SP (suc n)) {ρ} (t : A .F (ext ρ (Nu A .F ρ))) → Nu A .F ρ
inNu A {ρ} t = inf (A .mon (λ{i} → ext-forget i) t) (A .necc t ∘ A .anti-Supp (λ{i} → ext-forget i) t)

outNu : ∀{n} (A : SP (suc n)) {ρ} (t : Nu A .F ρ) → A .F (ext ρ (Nu A .F ρ))
outNu A {ρ} t = A .mon (λ{i} → ψ {i}) (A .suff x)
  where
  x = t .shape
  ψ : A .Supp {ext ρ ⊤} x →̇ ext ρ (Nu A .F ρ)
  ψ {zero} = t .child
  ψ {suc i} = A .necc x {suc i}

outNu∘inNu : ∀{n} (A : SP (suc n)) {ρ} (t : A .F (ext ρ (Nu A .F ρ))) → outNu A (inNu A t) ≡ t
outNu∘inNu {n} A {ρ} t = {!!}

coiterNu :  ∀{n} (A : SP (suc n)) {ρ} {C} (s : C → A .F (ext ρ C)) → C → Nu A .F ρ
coiterNu A {ρ} {C} s c .shape = A .mon (λ{i} → ext-forget i) (s c)
coiterNu A {ρ} {C} s c .child = coiterNu A s ∘ A .necc (s c) ∘ A .anti-Supp (λ{i} → ext-forget i) (s c)

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
tosp C .anti-Supp f (s , t) p = p
tosp C .necc (s , t) p = t p
tosp C .suff (s , t) = s , λ x → x
{-
tosp C .necc-suff = refl
tosp C .suff-necc p = refl
tosp C .suff-nat f xs = refl
tosp C .necc-nat f xs p = refl
tosp C .mon-comp xs = refl
tosp C .anti-Supp-comp = λ xs p → refl
-}

-- A stricly positive functor is isomorphic to a container
module M  (sp : SPos) where

  cont : Cont
  cont = sp .F ⊤ , sp .Supp

  G = ⟦ cont ⟧

  fwd : ∀ {X} → sp .F X → G X
  fwd fx = sp .mon _ fx  , λ p → sp .necc fx (sp .anti-Supp _ fx p)

  bwd : ∀ {X} → G X → sp .F X
  bwd (s , t) = sp .mon t (sp .suff s)

{-
  iso1 : ∀ {X} (xs : sp .F X) → bwd (fwd xs) ≡ xs
  iso1 xs = trans
            (trans (sym (sp .mon-comp (sp .suff (sp .mon _ xs))))
                   (cong (sp .mon (sp .necc xs)) (sp .suff-nat _ xs)))
                   (sp .necc-suff)

  iso2₁ : ∀ {X} (xs : G X) → (fwd (bwd xs)) .proj₁ ≡ xs .proj₁
  iso2₁ (s , t) = trans (sp .mon-comp (sp .suff s)) (sp .necc-suff)


  iso2₂ : ∀ {X} (xs : G X) {p : _} →
            (fwd (bwd xs)) .proj₂ p ≡ xs .proj₂ (subst (sp .Supp) (iso2₁ xs) p)
  iso2₂ (s , t) {p} = trans (sp .necc-nat  t (sp .suff s) _)
                  (cong t (trans
                          (cong (sp .necc (sp .suff s)) (sp .anti-Supp-comp (sp .suff s) _))
                                (trans (sp .suff-necc _)
                                       (sym (subst-trans ((sp .mon-comp (sp .suff s)))
                                                         (sp .necc-suff) p) ))))
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
