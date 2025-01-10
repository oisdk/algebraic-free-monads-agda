{-# OPTIONS --safe #-}

module Data.Sigma where

open import Agda.Builtin.Sigma
  using (Σ; fst; snd)
  renaming (_,_ to infixr 3 _,_)
  public
open import Level
open import Path
open import Data.Empty

infixr 3 ∃-syntax
∃-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃-syntax {A = A} = Σ A

syntax ∃-syntax (λ x → e) = ∃ x × e

infixr 3 ∄-syntax
∄-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∄-syntax {A = A} B = ¬ Σ A B

syntax ∄-syntax (λ x → e) = ∄ x × e

infixr 3 Σ⦂-syntax
Σ⦂-syntax : (A : Type a) (B : A → Type b) → Type (a ℓ⊔ b)
Σ⦂-syntax = Σ

syntax Σ⦂-syntax t (λ x → e) = Σ[ x ⦂ t ] × e

infixr 3 _×_
_×_ : (A : Type a) → (B : Type b) → Type (a ℓ⊔ b)
A × B = Σ A λ _ → B

Σ! : ∀ {a b} (A : Type a) (B : A → Type b) → Type (a ℓ⊔ b)
Σ! A B = Σ[ x ⦂ A ] × B x × (∀ y → B y → x ≡ y)

infixr 3 Σ!-syntax
Σ!-syntax : ∀ {a b} (A : Type a) (B : A → Type b) → Type (a ℓ⊔ b)
Σ!-syntax = Σ!

syntax Σ!-syntax t (λ x → e) = Σ![ x ⦂ t ] × e

∃! : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃! B = ∃ x × B x × (∀ y → B y → x ≡ y)

infixr 3 ∃!-syntax
∃!-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃!-syntax = ∃!

syntax ∃!-syntax (λ x → e) = ∃ ! x × e

curry : ∀ {A : Type a} {B : A → Type b} {C : Σ A B → Type c} →
          ((p : Σ A B) → C p) →
          ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)
{-# INLINE curry #-}

uncurry : ∀ {A : Type a} {B : A → Type b} {C : Σ A B → Type c} →
            ((x : A) → (y : B x) → C (x , y)) →
            ((p : Σ A B) → C p)
uncurry f x,y = f (x,y .fst) (x,y .snd)
{-# INLINE uncurry #-}

map-Σ : ∀ {p q} {P : A → Type p} {Q : B → Type q} →
        (f : A → B) → (∀ {x} → P x → Q (f x)) →
        Σ A P → Σ B Q
map-Σ f g (x , y) = f x , g y
{-# INLINE map-Σ #-}

map₁ : (A → B) → A × C → B × C
map₁ f = map-Σ f (λ x → x)
{-# INLINE map₁ #-}

map₁-Σ : ∀ {A : Type a} {B : Type b} {C : B → Type b}
       → (f : A → B) → Σ A (λ x → C (f x)) → Σ B C
map₁-Σ f (x , y) = f x , y
{-# INLINE map₁-Σ #-}

map₂ : ∀ {A : Type a} {B : A → Type b} {C : A → Type c} →
        (∀ {x} → B x → C x) → Σ A B → Σ A C
map₂ f = map-Σ (λ x → x) f
{-# INLINE map₂ #-}

_▵_ : (A → B) → (A → C) → A → B × C
(f ▵ g) x = f x , g x
