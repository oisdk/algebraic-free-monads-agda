{-# OPTIONS --safe #-}

module Data.Fin where

open import Level
open import Data.Nat
open import Data.Sigma
open import Data.Empty using (⊥)

private
  variable n : ℕ

data Fin⁺ (n : ℕ) : Type
Fin : ℕ → Type

Fin zero    = ⊥
Fin (suc n) = Fin⁺ n

data Fin⁺ n where
  suc : Fin n → Fin⁺ n
  zero : Fin⁺ n

open import Decidable
open import Data.Bool
open import Path

module DiscreteFin where
  _≡ᴮ_ : Fin n → Fin n → Bool
  _≡ᴮ_ {n = suc _} zero zero = true
  _≡ᴮ_ {n = suc _} (suc x) (suc y) = x ≡ᴮ y
  _≡ᴮ_ {n = suc _} _ _ = false

  sound : (x y : Fin n) → T (x ≡ᴮ y) → x ≡ y
  sound {n = suc _} zero    zero    p = refl
  sound {n = suc _} (suc x) (suc y) p = cong suc (sound x y p)

  complete : (x : Fin n) → T (x ≡ᴮ x)
  complete {n = suc _} zero    = _
  complete {n = suc _} (suc x) = complete x

discreteFin : Discrete (Fin n)
discreteFin = from-bool-eq record { DiscreteFin }

open import HLevels

isSetFin : isSet (Fin n)
isSetFin = Discrete→isSet discreteFin

open import Data.Nat.Order

FinFromℕ : ∀ m n → m < n → Fin n
FinFromℕ zero    (suc n) p = zero
FinFromℕ (suc m) (suc n) p = suc (FinFromℕ m n p)

FinToℕ : Fin n → Σ[ m ⦂ ℕ ] × m < n
FinToℕ {n = suc _} zero    = zero , _
FinToℕ {n = suc _} (suc x) = let x′ , p = FinToℕ x in suc x′ , p

open import Literals.Number

instance
  numberFin : ∀ {n} → Number (Fin n)
  numberFin {n} = record
    { Constraint = λ m → T (m <ᵇ n)
    ; fromNat    = λ m {{pr}} → FinFromℕ m n pr
    }

open import Data.Unit

_ : Fin 5
_ = 3

_ : Fin 1
_ = 0

pattern f0 = Fin⁺.zero
pattern f1 = suc f0
pattern f2 = suc f1
pattern f3 = suc f2
pattern f4 = suc f3
pattern f5 = suc f4
pattern f6 = suc f5
pattern f7 = suc f6
pattern f8 = suc f7
pattern f9 = suc f8
