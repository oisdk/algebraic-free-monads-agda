{-# OPTIONS --safe #-}

module Data.Unit.UniversePolymorphic.Properties where

open import Prelude
open import Cubical.Foundations.Everything using (isContr→isOfHLevel)

isOfHLevelPoly⊤ : ∀ n → isOfHLevel n (Poly-⊤ {ℓ = a})
isOfHLevelPoly⊤ n = isContr→isOfHLevel n (Poly-tt , λ _ → refl)

