{-# OPTIONS --cubical --safe #-}
module Algebra where

open import Prelude

module _ {a} {A : Type a} (_∙_ : A → A → A) where
  Associative : Type a
  Associative = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  Commutative : Type _
  Commutative = ∀ x y → x ∙ y ≡ y ∙ x

  Idempotent : Type _
  Idempotent = ∀ x → x ∙ x ≡ x

Identityˡ : (A → B → B) → A → Type _
Identityˡ _∙_ x = ∀ y → x ∙ y ≡ y

Zeroˡ : (A → B → A) → A → Type _
Zeroˡ _∙_ x = ∀ y → x ∙ y ≡ x

Zeroʳ : (A → B → B) → B → Type _
Zeroʳ _∙_ x = ∀ y → y ∙ x ≡ x

Identityʳ : (A → B → A) → B → Type _
Identityʳ _∙_ x = ∀ y → y ∙ x ≡ y

_Distributesʳ_ : (A → B → B) → (B → B → B) → Type _
_⊗_ Distributesʳ _⊕_ = ∀ x y z → x ⊗ (y ⊕ z) ≡ (x ⊗ y) ⊕ (x ⊗ z)

_Distributesˡ_ : (B → A → B) → (B → B → B) → Type _
_⊗_ Distributesˡ _⊕_ = ∀ x y z → (x ⊕ y) ⊗ z ≡ (x ⊗ z) ⊕ (y ⊗ z)

Cancellableˡ : (A → B → C) → A → Type _
Cancellableˡ _⊗_ c = ∀ x y → c ⊗ x ≡ c ⊗ y → x ≡ y

Cancellableʳ : (A → B → C) → B → Type _
Cancellableʳ _⊗_ c = ∀ x y → x ⊗ c ≡ y ⊗ c → x ≡ y

Cancellativeˡ : (A → B → C) → Type _
Cancellativeˡ _⊗_ = ∀ c → Cancellableˡ _⊗_ c

Cancellativeʳ : (A → B → C) → Type _
Cancellativeʳ _⊗_ = ∀ c → Cancellableʳ _⊗_ c

record  Semigroup ℓ : Type (ℓsuc ℓ) where
  infixl 6 _∙_
  field
    𝑆      : Type ℓ
    _∙_    : 𝑆 → 𝑆 → 𝑆
    assoc  : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

record  Monoid ℓ : Type (ℓsuc ℓ) where
  infixl 6 _∙_
  field
    𝑆      : Type ℓ
    _∙_    : 𝑆 → 𝑆 → 𝑆
    ε      : 𝑆
    assoc  : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    ε∙     : ∀ x → ε ∙ x ≡ x
    ∙ε     : ∀ x → x ∙ ε ≡ x

  semigroup : Semigroup ℓ
  semigroup = record
    { 𝑆 = 𝑆; _∙_ = _∙_; assoc = assoc }

record MonoidHomomorphism_⟶_
         {ℓ₁ ℓ₂}
         (from : Monoid ℓ₁)
         (to : Monoid ℓ₂)
       : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  open Monoid from
  open Monoid to
    renaming ( 𝑆 to 𝑅
             ; _∙_ to _⊙_
             ; ε to ⓔ
             )
  field
    f : 𝑆 → 𝑅
    ∙-homo : ∀ x y → f (x ∙ y) ≡ f x ⊙ f y
    ε-homo : f ε ≡ ⓔ

record Group ℓ : Type (ℓsuc ℓ) where
  field
    monoid : Monoid ℓ
  open Monoid monoid public
  field
    -_ : 𝑆 → 𝑆
    ∙⁻ : ∀ x → x ∙ - x ≡ ε
    ⁻∙ : ∀ x → - x ∙ x ≡ ε

  open import Path.Reasoning

  cancelˡ : Cancellativeˡ _∙_
  cancelˡ x y z p =
    y ≡˘⟨ ε∙ y ⟩
    ε ∙ y ≡˘⟨ cong (_∙ y) (⁻∙ x) ⟩
    (- x ∙ x) ∙ y ≡⟨ assoc (- x) x y ⟩
    - x ∙ (x ∙ y) ≡⟨ cong (- x ∙_) p ⟩
    - x ∙ (x ∙ z) ≡˘⟨ assoc (- x) x z ⟩
    (- x ∙ x) ∙ z ≡⟨ cong (_∙ z) (⁻∙ x) ⟩
    ε ∙ z ≡⟨ ε∙ z ⟩
    z ∎

  cancelʳ : Cancellativeʳ _∙_
  cancelʳ x y z p =
    y ≡˘⟨ ∙ε y ⟩
    y ∙ ε ≡˘⟨ cong (y ∙_) (∙⁻ x) ⟩
    y ∙ (x ∙ - x) ≡˘⟨ assoc y x (- x) ⟩
    (y ∙ x) ∙ - x ≡⟨ cong (_∙ - x) p ⟩
    (z ∙ x) ∙ - x ≡⟨ assoc z x (- x) ⟩
    z ∙ (x ∙ - x) ≡⟨ cong (z ∙_) (∙⁻ x) ⟩
    z ∙ ε ≡⟨ ∙ε z ⟩
    z ∎

record CommutativeMonoid ℓ : Type (ℓsuc ℓ) where
  field
    monoid : Monoid ℓ
  open Monoid monoid public
  field
    comm : Commutative _∙_

record Semilattice ℓ : Type (ℓsuc ℓ) where
  field
    commutativeMonoid : CommutativeMonoid ℓ
  open CommutativeMonoid commutativeMonoid public
  field
    idem : Idempotent _∙_
