{-# OPTIONS --safe #-}

module Level where

open import Agda.Primitive
  using (Level)
  renaming ( _⊔_ to _ℓ⊔_
           ; lzero to ℓzero
           ; lsuc  to ℓsuc
           ; Set to Type
           ; Setω to Typeω
           )
  public

variable
  a b c : Level
  A  : Type a
  B  : Type b
  C  : Type c
  p : Level
  P : A → Type p

Type- : ∀ {ℓ} → Type (ℓsuc ℓ)
Type- {ℓ} = Type ℓ
