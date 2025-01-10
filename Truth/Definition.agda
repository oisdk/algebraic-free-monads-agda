{-# OPTIONS --safe #-}

open import Prelude
  hiding (⊤; tt; Poly-⊤; Poly-tt; ⊥; Poly-⊥)

module Truth.Definition (ℓ : Level) where

open import Data.Unit.UniversePolymorphic {ℓ}
open import Data.Empty.UniversePolymorphic {ℓ}

infix 3 _∥_
record Ω : Type (ℓsuc ℓ) where
  constructor _∥_; no-eta-equality
  field  ProofOf  : Type ℓ
         IsProp   : isProp ProofOf
open Ω public
