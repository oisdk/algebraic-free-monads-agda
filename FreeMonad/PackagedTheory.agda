{-# OPTIONS --safe #-}

module FreeMonad.PackagedTheory where

open import Prelude
open import Signatures
open import FreeMonad.Theory
open import FinitenessConditions

record FullTheory ℓ : Typeω where
  constructor full-theory
  field
    𝔽 : Signature
    𝒯 : Theory ℓ 𝔽
    finiteArity : ∀ Oᵢ → SplitQuotientedChoiceω (Signature.Arity 𝔽 Oᵢ)
    finiteVars : FiniteVars 𝒯

open FullTheory
open Signature
open Theory

--------------------------------------------------------------------------------
-- Standard first-order finitary algebraic theories have both finite
-- arities and equation variables.
--------------------------------------------------------------------------------
record FiniteTheory (theory : FullTheory ℓzero) : Type₁  where
  field
    finArities : ∀ o → ∃ n × (Fin n ≡ theory .𝔽 .Arity o)
    finVars : (l : theory .𝒯 .Laws) → let law = theory .𝒯 .Eqns l in
              (γ : Γ law) → ∃ n × (Fin n ≡ ν law γ)
