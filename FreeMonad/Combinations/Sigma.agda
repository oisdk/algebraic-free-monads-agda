{-# OPTIONS --safe #-}

open import Prelude
open import FreeMonad.PackagedTheory
open import Signatures
open import FinitenessConditions

module FreeMonad.Combinations.Sigma
  {ℓ}
  (I : Type)
  (Tₙ : I → FullTheory ℓ)
  where

open Signature

open import FreeMonad.Theory
open import FreeMonad.Syntax

𝔽⊙ : I → Signature
𝔽⊙ i = FullTheory.𝔽 (Tₙ i)

module _ (i : I) where

  open FullTheory (Tₙ i) public renaming (𝒯 to 𝒯ₙ)

  inj : Syntax 𝔽 A → Syntax (Σ◁ I 𝔽⊙) A
  inj = interp 𝔽 (λ { (O , xs) → op ((i , O) , xs) }) var

  lawₙ : Law ℓ 𝔽 → Law ℓ (Σ◁ I 𝔽⊙)
  lawₙ e .Γ = _
  lawₙ e .ν = _
  lawₙ e .eqn γ = let lhs ≐ rhs = e .eqn γ in inj lhs ≐ inj rhs

open Theory

𝒯 : Theory ℓ (Σ◁ I 𝔽⊙)
𝒯 .Laws = Σ[ i ⦂ I ] × Laws (𝒯ₙ i)
𝒯 .Eqns = uncurry lawₙ ∘ map₂ (Eqns (𝒯ₙ _))

finArity : ∀ Oᵢ → SplitQuotientedChoiceω (Arity (Σ◁ I 𝔽) Oᵢ)
finArity (i , O) = finiteArity i O

finVars : FiniteVars 𝒯
finVars (i , O) γ = finiteVars i O γ

combinedTheory : FullTheory ℓ
combinedTheory .FullTheory.𝔽 = Σ◁ I 𝔽
combinedTheory .FullTheory.𝒯 = 𝒯
combinedTheory .FullTheory.finiteArity = finArity
combinedTheory .FullTheory.finiteVars = finVars
