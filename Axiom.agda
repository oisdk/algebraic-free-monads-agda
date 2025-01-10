{-# OPTIONS --safe #-}

module Axiom where

-- This module includes definitions of the various axioms independent of HoTT
-- and their consequences. Bear in mind these are just the definitions of the
-- axioms, not postulates of them; in other words, this file is totally safe.

open import HITs.PropositionalTruncation
open import Level
open import HLevels

module _ (A : Type a) (P : A → Type b) where
  ChoiceOver : Type (a ℓ⊔ b)
  ChoiceOver =
    ((x : A) → ∥ P x ∥) → ∥ ((x : A) → P x) ∥

Choice : (A : Type a) → ∀ b → Type (a ℓ⊔ ℓsuc b)
Choice A b = ∀ {B : A → Type b} → ChoiceOver A B

isPropChoice : isProp (Choice A b)
isPropChoice x y i f = squash (x f) (y f) i

Choiceω : (A : Type a) → Typeω
Choiceω A = ∀ {b} → Choice A b

AOC : ∀ ℓ₁ ℓ₂ → Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂))
AOC ℓ₁ ℓ₂ = ∀ {A : Type ℓ₁} {B : A → Type ℓ₂} → isSet A → ChoiceOver A B

AOCω : Typeω
AOCω = ∀ {ℓ₁ ℓ₂} → AOC ℓ₁ ℓ₂

open import Decidable
open import Data.Sigma

Omniscient : Type a → Typeω
Omniscient A = ∀ {p} {P : A → Type p} → (∀ x → Dec (P x)) → Dec (∃ x × P x)
