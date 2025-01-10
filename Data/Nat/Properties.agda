{-# OPTIONS --safe #-}

module Data.Nat.Properties where

open import Prelude
open import Agda.Builtin.Nat using (_+_; _-_) public

case-nat : (P : ℕ → Type p)
         → P zero
         → (∀ n → P (suc n))
         → ∀ n → P n
case-nat P z s zero    = z
case-nat P z s (suc n) = s n

case-nat′ : A → (ℕ → A) → ℕ → A
case-nat′ = case-nat _

is-zero : ℕ → Bool
is-zero = case-nat′ true (const false)

private variable n m : ℕ

zero≢suc : zero ≢ suc n
zero≢suc = true≢false ∘ cong is-zero

suc≢zero : suc n ≢ zero
suc≢zero = false≢true ∘ cong is-zero

module DiscreteNat where
  _≡ᴮ_ : ℕ → ℕ → Bool
  zero  ≡ᴮ zero  = true
  suc x ≡ᴮ suc y = x ≡ᴮ y
  _     ≡ᴮ _     = false

  sound : (x y : ℕ) → T (x ≡ᴮ y) → x ≡ y
  sound zero    zero    p = refl
  sound (suc x) (suc y) p = cong suc (sound x y p)

  complete : (x : ℕ) → T (x ≡ᴮ x)
  complete zero    = _
  complete (suc x) = complete x

discreteNat : Discrete ℕ
discreteNat = from-bool-eq record { DiscreteNat }

isSetNat : isSet ℕ
isSetNat = Discrete→isSet discreteNat

suc-inj : suc n ≡ suc m → n ≡ m
suc-inj {n = n} = cong (case-nat′ n id)

+-suc : ∀ n m → n + suc m ≡ suc n + m
+-suc zero m = refl
+-suc (suc n) m = cong suc (+-suc n m)

+-zero : ∀ n → n + zero ≡ n
+-zero zero = refl
+-zero (suc n) = cong suc (+-zero n)

+-comm : ∀ n m → n + m ≡ m + n
+-comm zero m = sym (+-zero m)
+-comm (suc n) m = cong suc (+-comm n m) ⨾ sym (+-suc m n)

data Ordering : ℕ → ℕ → Type where
  less    : ∀ m k → Ordering m (suc (m + k))
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m

compare : ∀ m n → Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
... | less    m k = less (suc m) k
... | equal   m   = equal (suc m)
... | greater n k = greater (suc n) k

NonZero : ℕ → Type
NonZero zero    = ⊥
NonZero (suc n) = ⊤

open import Agda.Builtin.Nat using (mod-helper)

_mod_ : (n m : ℕ) → ⦃ _ : NonZero m ⦄ → ℕ
n mod suc m = mod-helper 0 m n m
