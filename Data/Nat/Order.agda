{-# OPTIONS --safe #-}

module Data.Nat.Order where

open import Agda.Builtin.Nat renaming (_<_ to _<ᵇ_) public
open import Data.Bool
open import Data.Nat
open import Level

infix 4 _<_ _≤ᵇ_ _≤_ _>_ _≥_

_<_ : ℕ → ℕ → Type
n < m = T (n <ᵇ m)

_≤ᵇ_ : ℕ → ℕ → Bool
n ≤ᵇ m = n <ᵇ suc m

_≤_ : ℕ → ℕ → Type
n ≤ m = T (n ≤ᵇ m)

_>_ _≥_ : ℕ → ℕ → Type

n > m = m < n
n ≥ m = m ≤ n

open import HLevels
open import Data.Bool.Properties

isProp≤ : ∀ {n m} → isProp (n ≤ m)
isProp≤ = isPropT _
