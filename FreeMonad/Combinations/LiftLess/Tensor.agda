{-# OPTIONS --safe #-}

open import Prelude
open import FreeMonad.PackagedTheory
open import Signatures
open import FinitenessConditions

module FreeMonad.Combinations.LiftLess.Tensor
  (T₁ : FullTheory ℓzero)
  (T₂ : FullTheory ℓzero)
  where

import FreeMonad.Combinations.Sum T₁ T₂ as SumTheory

open import FreeMonad.Combinations.Sum T₁ T₂
  hiding (𝒯; finVars; lift₁; lift₂; combinedTheory)
  public

open FullTheory T₁ renaming (𝒯 to 𝒯₁; finiteArity to finAr₁; finiteVars to finVar₁)
open FullTheory T₂ renaming (𝔽 to 𝔾; 𝒯 to 𝒯₂; finiteArity to finAr₂; finiteVars to finVar₂)

open Signature

open import FreeMonad.Syntax hiding (Op⟦_⟧)
open import FreeMonad.Theory 0 (𝔽 ⊞ 𝔾)
open import FreeMonad.Syntax (𝔽 ⊞ 𝔾) using (Op⟦_⟧)

open SyntaxBind (𝔽 ⊞ 𝔾)

commutative : Law
commutative .Γ = Op 𝔽 × Op 𝔾
commutative .ν (fs , gs) = Arity 𝔽 fs × Arity 𝔾 gs
commutative .eqn (fs , gs) =
  (do f  ← Op⟦ inl fs  ⟧ ; g  ← Op⟦ inr gs  ⟧ ; return (f , g))
                               ≐
  (do g  ← Op⟦ inr gs  ⟧ ; f  ← Op⟦ inl fs  ⟧ ; return (f , g))
