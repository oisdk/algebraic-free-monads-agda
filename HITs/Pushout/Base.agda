{-# OPTIONS --safe #-}

open import Prelude

module HITs.Pushout.Base {A : Type a} {B : Type b} {C : Type c} (f : A → B) (g : A → C) where

data Pushout : Type (a ℓ⊔ b ℓ⊔ c) where
  inl : B → Pushout
  inr : C → Pushout
  push : ∀ x → inl (f x) ≡ inr (g x)
  trunc : isSet Pushout

pull : B ⊎ C → Pushout
pull = inl ▿ inr
