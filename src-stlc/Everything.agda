-- Simply-typed lambda definability and normalization by evaluation
-- formalized in Agda
--
-- Author: Andreas Abel, May/June 2018

module Everything where

-- 0. Standard library imports and auxiliary definitions

import Library

-- 1. A universe of simple types; contexts and order-preserving embeddings

import SimpleTypes

-- 2. Simply-typed lambda calculus (STLC) definability:
-- 2a. STLC-definability via Kripke predicates for STLC with constants
-- 2b. Intrinsically typed variables and terms and their interpretation
-- 2c. Reflect/reify: a term model proving that soundness of definability
-- 2d. Fundamental theorem of logical relations proving completeness

import STLCDefinable
import DefinitionalEquality

-- 3. Adapting reflection/reification to obtain normalization

import NBE

-- 4. Using Kripke predicates to refute STLC-definability...
-- 4a. ... of boolean negation

-- import NotNotDefinable

-- 4b. ... of an inhabitant of Peirce's formula

-- import PeirceNotDefinable
