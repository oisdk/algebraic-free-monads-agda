{-# OPTIONS --safe #-}

module Level.Literals where

open import Level
open import Literals.Number
open import Data.Nat
open import Data.Unit

Levelfromℕ : ℕ → Level
Levelfromℕ zero    = ℓzero
Levelfromℕ (suc n) = ℓsuc (Levelfromℕ n)

instance
  numberLevel : Number Level
  numberLevel = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → Levelfromℕ n
    }
