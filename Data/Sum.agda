{-# OPTIONS --without-K --safe #-}

module Data.Sum where

open import Level
open import Function

infixr 3 _⊎_
data _⊎_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

either : ∀ {ℓ} {C : A ⊎ B → Type ℓ} →  ((a : A) → C (inl a)) → ((b : B) → C (inr b))
        → (x : A ⊎ B) → C x
either f _ (inl x) = f x
either _ g (inr y) = g y

either′ : (A → C) → (B → C) → (A ⊎ B) → C
either′ = either

_▿_ : (A → C) → (B → C) → A ⊎ B → C
(f ▿ g) (inl  x) = f x
(f ▿ g) (inr  x) = g x

map-⊎ : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂} {B₁ : Type b₁} {B₂ : Type b₂} →
      (A₁ → A₂) →
      (B₁ → B₂) →
      (A₁ ⊎ B₁) →
      (A₂ ⊎ B₂)
map-⊎ f g = either (inl ∘ f) (inr ∘ g)

mapˡ : (A → B) → A ⊎ C → B ⊎ C
mapˡ f = map-⊎ f id

mapʳ : (A → B) → C ⊎ A → C ⊎ B
mapʳ = map-⊎ id

open import Path

inl-inj : Injective (inl {A = A} {B = B})
inl-inj {y = y} = cong (either′ id (const y))

inr-inj : Injective (inr {A = A} {B = B})
inr-inj {x = x} = cong (either′ (const x) id)

open import Data.Bool
open import Data.Bool.Properties

is-l : A ⊎ B → Bool
is-l = either′ (const true) (const false)

inr≢inl : {x : A} {y : B} → inr x ≢ inl y
inr≢inl = false≢true ∘ cong is-l

inl≢inr : {x : A} {y : B} → inl x ≢ inr y
inl≢inr = true≢false ∘ cong is-l

open import Decidable
open import Data.Sigma

Discrete-⊎ : Discrete A → Discrete B → Discrete (A ⊎ B)
Discrete-⊎ lhs _ (inl x) (inl y) = iff-dec (cong inl , inl-inj) (lhs x y)
Discrete-⊎ _ _ (inl x) (inr x₁) = no inl≢inr
Discrete-⊎ _ _ (inr x) (inl x₁) = no inr≢inl
Discrete-⊎ _ rhs (inr x) (inr y) = iff-dec (cong inr , inr-inj) (rhs x y)
