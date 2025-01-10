{-# OPTIONS --safe #-}

module Data.Empty where

open import Level
open import Cubical.Data.Empty using (⊥) public

infixr 5 ¬_
¬_ : Type a → Type a
¬ A = A → ⊥

absurd : ∀ {A : Type a} → ⊥ → A
absurd ()
