{-# OPTIONS --safe #-}

module Data.Tree where

open import Prelude

data Tree : Type where
  ♢ ♠  : Tree
  _⊛_  : Tree → Tree → Tree

module TreeEq where
  _≡ᴮ_ : Tree → Tree → Bool
  ♢ ≡ᴮ ♢ = true
  ♠ ≡ᴮ ♠ = true
  (xˡ ⊛ xʳ) ≡ᴮ (yˡ ⊛ yʳ) = (xˡ ≡ᴮ yˡ) && (xʳ ≡ᴮ  yʳ)
  _ ≡ᴮ _ = false

  &&-× : {x y : Bool} → T (x && y) → T x × T y
  &&-× {true} {true} _ = tt , tt

  sound : ∀ x y → T (x ≡ᴮ y) → x ≡ y
  sound ♢ ♢ p = refl
  sound ♠ ♠ p = refl
  sound (xˡ ⊛ xʳ) (yˡ ⊛ yʳ) p = let l , r = &&-× p in cong₂ _⊛_ (sound xˡ yˡ l) (sound xʳ yʳ r)

  ×-&& : {x y : Bool} → T x → T y → T (x && y)
  ×-&& {true} {true} _ _ = tt

  complete : ∀ x → T (x ≡ᴮ x)
  complete ♢ = tt
  complete ♠ = tt
  complete (x ⊛ y) = ×-&& (complete x) (complete y)

tree-eq : Discrete Tree
tree-eq = from-bool-eq record { TreeEq }

left : Tree → Maybe Tree
left (x ⊛ _) = just x
left _ = nothing

right : Tree → Maybe Tree
right (_ ⊛ x) = just x
right _ = nothing
