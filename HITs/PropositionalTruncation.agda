{-# OPTIONS --safe #-}

module HITs.PropositionalTruncation where

open import Cubical.HITs.PropositionalTruncation
  -- using (squash; ∥_∥; ∣_∣)
  renaming
    ( squash₁ to squash
    ; ∥_∥₁ to ∥_∥
    ; ∣_∣₁ to ∣_∣
    ; rec to ∥rec∥
    ; rec2 to ∥rec2∥
    ; elim to ∥elim∥
    ; rec→Set to ∥rec∥→Set
    )
  public

open import Level
open import Function

∥map∥ : (A → B) → ∥ A ∥ → ∥ B ∥
∥map∥ f = ∥rec∥ squash (∣_∣ ∘ f)

∥liftA2∥ : (A → B → C) → ∥ A ∥ → ∥ B ∥ → ∥ C ∥
∥liftA2∥ f = ∥rec2∥ squash λ x y → ∣ f x y ∣

∥bind∥ : (A → ∥ B ∥) → ∥ A ∥ → ∥ B ∥
∥bind∥ = ∥rec∥ squash
