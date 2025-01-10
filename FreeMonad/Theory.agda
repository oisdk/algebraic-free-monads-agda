{-# OPTIONS --safe #-}

open import Prelude
open import Signatures
open import FinitenessConditions
open import FreeMonad.Syntax

--------------------------------------------------------------------------------
-- Equations and theories for computations
--------------------------------------------------------------------------------

module FreeMonad.Theory (ℓ : Level) (𝔽 : Signature) where

open import FreeMonad.Equation public

--------------------------------------------------------------------------------
-- A law (equation with the type params as existentials)
--------------------------------------------------------------------------------

record Law : Type (ℓsuc ℓ) where
  field  Γ  : Type ℓ
         ν  : Γ → Type ℓ
         eqn : (γ : Γ) → Equation 𝔽 (ν γ)
open Law public

--------------------------------------------------------------------------------
-- A theory
--------------------------------------------------------------------------------

record Theory : Type (ℓsuc ℓ) where
  constructor _◁≡_
  field  Laws  : Type
         Eqns  : Laws → Law

--------------------------------------------------------------------------------
-- A theory needs to have finitely many variables
--------------------------------------------------------------------------------

  FiniteVars =
    ∀ i →
    let law = Eqns i in
    (γ : Γ law) →
    SplitQuotientedChoiceω (ν law γ)

  --------------------------------------------------------------------------------
  -- In some cases we need variables to have decidable equality
  --------------------------------------------------------------------------------

  DiscreteVars =
    ∀ i →
    let law = Eqns i in
    (γ : Γ law) →
    Discrete (ν law γ)

  --------------------------------------------------------------------------------
  -- Algebras can "respect" an equation or a full theory
  --------------------------------------------------------------------------------

  infix 4 ModelledBy
  ModelledBy : 𝔽 -Alg[ A ] → Type _
  ModelledBy ϕ = ∀ i γ → ϕ Respects Eqns i .eqn γ

  syntax ModelledBy 𝒯 ϕ = ϕ Models 𝒯

  _-Model[_] : Type b → Type _
  _-Model[_] 𝒞 = Σ[ ϕ ⦂ 𝔽 -Alg[ 𝒞 ] ] × ModelledBy ϕ

open Theory
  hiding (Laws; Eqns)
  public
