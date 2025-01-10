{-# OPTIONS --safe #-}

open import Prelude
open import FreeMonad.PackagedTheory
open import Signatures
open import FinitenessConditions
import FreeMonad.Theory

module FreeMonad.Combinations.Quotient
  {ℓ}
  (T : FullTheory ℓ)
  (𝒯′ : FreeMonad.Theory.Theory ℓ (FullTheory.𝔽 T))
  (finVars′ : FreeMonad.Theory.FiniteVars  𝒯′)
  where

open FullTheory T renaming (𝒯 to 𝒯″)
open module 𝕋 = FreeMonad.Theory ℓ 𝔽

𝒯 : Theory
𝒯 .Theory.Laws = 𝒯″ .Theory.Laws ⊎ 𝒯′ .Theory.Laws
𝒯 .Theory.Eqns = 𝒯″ .Theory.Eqns ▿ 𝒯′ .Theory.Eqns

finVars : FiniteVars 𝒯
finVars (inl x) = finiteVars x
finVars (inr x) = finVars′ x

combinedTheory : FullTheory ℓ
combinedTheory .FullTheory.𝔽 = 𝔽
combinedTheory .FullTheory.𝒯 = 𝒯
combinedTheory .FullTheory.finiteArity = finiteArity
combinedTheory .FullTheory.finiteVars = finVars

open import FreeMonad.Quotiented combinedTheory

import FreeMonad.Quotiented T as F′
open import FreeMonad.Syntax

embed : F′.Term A → Term A
embed = rec/ squash/ [_] (λ xs ys r → eq/ xs ys (resp r))
  where
  resp : {xs ys : Syntax 𝔽 A} → xs F′.~ₜ ys → xs ~ₜ ys
  resp (reflₜ x) = reflₜ x
  resp (symₜ r) = symₜ (resp r)
  resp (transₜ p q) = transₜ (resp p) (resp q)
  resp (congₜ Oᵢ kₗ kᵣ x) = congₜ Oᵢ kₗ kᵣ λ i → resp (x i)
  resp (eqₜ i g k) = eqₜ (inl i) g k
  resp (truncₜ p q i) = truncₜ (resp p) (resp q) i
