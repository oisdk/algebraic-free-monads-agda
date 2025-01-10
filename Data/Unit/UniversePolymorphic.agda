{-# OPTIONS --safe #-}

open import Level

module Data.Unit.UniversePolymorphic {ℓ : Level} where

record ⊤ : Type ℓ where
  instance constructor tt
