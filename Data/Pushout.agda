{-# OPTIONS --safe #-}

module Data.Pushout where

open import Level
open import HLevels
open import Path
open import Function
open import Data.Sigma
open import Path.Reasoning

data SetPushout {A : Type a} {B : Type b} {C : Type c}
                (f : A → B) (g : A → C) : Type (a ℓ⊔ b ℓ⊔ c) where
  inl    : B → SetPushout f g
  inr    : C → SetPushout f g
  push   : (a : A) → inl (f a) ≡ inr (g a)
  trunc : isSet (SetPushout f g)

module _
  {f : A → B} {g : A → C}
  (P : SetPushout f g → Type p)
  (prop : (x : SetPushout f g) → isProp (P x))
  (PB : (b : B) → P (inl b))
  (PC : (c : C) → P (inr c)) where

  elimProp : (x : SetPushout f g) → P x
  elimProp (inl x) = PB x
  elimProp (inr x) = PC x
  elimProp (push a i) = isOfHLevel→isOfHLevelDep 1 prop (PB (f a)) (PC (g a)) (push a) i
  elimProp (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2
      (λ x → isProp→isSet (prop x))
      (elimProp xs) (elimProp ys)
      (cong elimProp p) (cong elimProp q)
      (trunc xs ys p q)
      i j

module _ {ℓ} {X : Type ℓ} {f : A → B} {g : A → C}
         (set : isSet X)
         (h₁ : B → X) (h₂ : C → X)
         (cancel : h₁ ∘ f ≡ h₂ ∘ g)
         where
  rec : SetPushout f g → X
  rec (inl x) = h₁ x
  rec (inr x) = h₂ x
  rec (push a i) = cancel i a
  rec (trunc xs ys p q i j) =
    set (rec xs) (rec ys) (cong rec p) (cong rec q) i j

  ump : Σ![ u ⦂ (SetPushout f g → X) ] × (u ∘ inl ≡ h₁) × (u ∘ inr ≡ h₂)
  ump .fst = rec
  ump .snd .fst .fst = refl
  ump .snd .fst .snd = refl
  ump .snd .snd y (l , r) = 
    funExt (elimProp
              _
              (λ _ → set _ _)
              (λ a → cong (_$ a) (sym l))
              (λ c → cong (_$ c) (sym r)))
