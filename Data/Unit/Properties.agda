{-# OPTIONS --safe #-}

module Data.Unit.Properties where

open import Data.Unit
open import HLevels
open import Path

isProp⊤ : isProp ⊤
isProp⊤ _ _ = refl

open import Cubical.Foundations.Everything using (isContr→isOfHLevel; _,_)

isOfHLevel⊤ : ∀ n → isOfHLevel n ⊤
isOfHLevel⊤ n = isContr→isOfHLevel n (tt , λ _ → refl)
