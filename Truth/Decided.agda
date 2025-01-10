{-# OPTIONS --safe #-}

module Truth.Decided where

open import Prelude
open import Truth.Definition
open import Truth.Combinators

Decided : ∀ ℓ → Type (ℓsuc ℓ)
Decided ℓ = Σ[ P ⦂ Ω ℓ ] × Dec (P .ProofOf)

module IsoDec {a : Level} where
  inv-fnc : Bool → Decided a
  inv-fnc = bool (False , no λ ()) (True , yes _)

  left-inv : (x : Decided a) → inv-fnc (does (x .snd)) .fst ≡ x .fst
  left-inv (P , yes p) = sym (proves p)
  left-inv (P , no ¬p) = sym (disproves ¬p)

  DecΩ⇔Bool : Decided a ⇔ Bool
  DecΩ⇔Bool .fun (_ , x) = does x
  DecΩ⇔Bool .inv = inv-fnc
  DecΩ⇔Bool .rightInv false = refl
  DecΩ⇔Bool .rightInv true  = refl
  DecΩ⇔Bool .leftInv  x = Σ≡Prop (λ p → isPropDec (p .IsProp)) (left-inv x)

  DecΩ≡Bool : Decided a ≡ Lift Bool
  DecΩ≡Bool = isoToPath (DecΩ⇔Bool ⟨ trans-⇔ ⟩ lift⇔)
open IsoDec public using (DecΩ⇔Bool; DecΩ≡Bool)
