-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, May/June 2018

-- 0. Standard library imports and auxiliary definitions

-- We use Agda's rewriting facility to automatically apply proven equalities.

{-# OPTIONS --rewriting #-}

module Library where

open import Data.Empty                            public using (⊥; ⊥-elim)
open import Data.Unit                             public using (⊤)
open import Data.Product                          public using (∃; _×_; _,_; proj₁; proj₂; curry)
open import Function                              public using (id; _∘_; _∘′_; case_of_)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl; subst; cong; sym)

{-# BUILTIN REWRITE _≡_ #-}

-- Product of functions

_×̇_ : ∀{A B C D : Set} → (A → C) → (B → D) → A × B → C × D
(f ×̇ g) (x , y) = f x , g y

-- Application (S-combinator)

apply : ∀{A B C : Set} (f : C → A → B) (d : C → A) → C → B
apply f a = λ c → f c (a c)
