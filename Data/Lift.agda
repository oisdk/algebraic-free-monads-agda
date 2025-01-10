{-# OPTIONS --safe #-}

module Data.Lift where

open import Level

record Lift {ℓ₁ ℓ₂} (A : Type ℓ₁) : Type (ℓ₁ ℓ⊔ ℓ₂) where
  constructor lift
  field lower : A
open Lift public

open import Isomorphism

lift⇔ : A ⇔ Lift {ℓ₂ = b} A
lift⇔ .fun = lift
lift⇔ .inv = lower
lift⇔ .rightInv x i = x
lift⇔ .leftInv  x i = x
