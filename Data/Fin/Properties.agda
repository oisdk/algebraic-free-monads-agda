{-# OPTIONS --safe #-}

module Data.Fin.Properties where

open import Prelude
open import Data.Pushout
open import Relation.Binary

private variable
  n : ℕ

import Data.Nat.Order as ℕ

infix 4 _<ᵇ_ _<_ _≮ᵇ_ _≮_ _≤ᵇ_ _≤_
_<ᵇ_ : Fin n → Fin n → Bool
n <ᵇ m = FinToℕ n .fst ℕ.<ᵇ FinToℕ m .fst

_<_ : Fin n → Fin n → Type
n < m = T (n <ᵇ m)

_≮ᵇ_ : Fin n → Fin n → Bool
n ≮ᵇ m = ! (n <ᵇ m)

_≮_ : Fin n → Fin n → Type
n ≮ m = T (n ≮ᵇ m)

_≤ᵇ_ : Fin n → Fin n → Bool
n ≤ᵇ m = FinToℕ n .fst ℕ.≤ᵇ FinToℕ m .fst

_≤_ : Fin n → Fin n → Type
n ≤ m = T (n ≤ᵇ m)

suc-injective : (x y : Fin n) → (suc x ⦂ Fin (suc n)) ≡ suc y → x ≡ y
suc-injective x y = cong {A = Fin _} λ { zero → x ; (suc z) → z }

foldFin : ∀ {n} → A → (Fin n → A → A) → A
foldFin {n = zero} e f = e
foldFin {n = suc n} e f = f zero (foldFin e (λ x a → f (suc x) a))

import Data.Nat.Properties as ℕ

zero≢suc : {x : Fin n} → (zero ⦂ Fin (suc n)) ≢ suc x
zero≢suc = ℕ.zero≢suc ∘ cong (fst ∘ FinToℕ)

suc≢zero : {x : Fin n} → (suc x ⦂ Fin (suc n)) ≢ zero
suc≢zero = ℕ.suc≢zero ∘ cong (fst ∘ FinToℕ)

private variable m : ℕ
open import Isomorphism.Properties

Fin⊥ : Fin 0 ⇔ ⊥
Fin⊥ .fun ()
Fin⊥ .inv ()
Fin⊥ .rightInv ()
Fin⊥ .leftInv ()

isPropFin1 : isProp (Fin 1)
isPropFin1 zero zero = refl

Finsuc : Fin (suc n) ⇔ (⊤ ⊎ Fin n)
Finsuc .fun zero = inl tt
Finsuc .fun (suc n) = inr n
Finsuc .inv (inl x) = zero
Finsuc .inv (inr x) = suc x
Finsuc .rightInv (inl x) = refl
Finsuc .rightInv (inr x) = refl
Finsuc .leftInv zero = refl
Finsuc .leftInv (suc x) = refl

fin-+ : (Fin n ⊎ Fin m) ⇔ Fin (n ℕ.+ m)
fin-+ {n = zero}  {m = m} = cong-⇔ (_⊎ Fin m) Fin⊥ ⟨ trans-⇔ ⟩ ⊎-idˡ
fin-+ {n = suc n} {m = m} = cong-⇔ (_⊎ Fin m) Finsuc
                 ⟨ trans-⇔ ⟩ ⊎-assoc
                 ⟨ trans-⇔ ⟩ cong-⇔ (⊤ ⊎_) fin-+
                 ⟨ trans-⇔ ⟩ sym-⇔ Finsuc

fin-× : (Fin n × Fin m) ⇔ Fin (n ℕ.* m)
fin-× {n = zero } {m = m} = cong-⇔ (_× Fin m) Fin⊥ ⟨ trans-⇔ ⟩ ×-annˡ ⟨ trans-⇔ ⟩ sym-⇔ Fin⊥
fin-× {n = suc n} {m = m} = cong-⇔ (_× Fin m) Finsuc
                ⟨ trans-⇔ ⟩ swap-×
                ⟨ trans-⇔ ⟩ ×-distrib-⊎
                ⟨ trans-⇔ ⟩ cong-⇔ (_⊎ (Fin m × Fin n)) (swap-× ⟨ trans-⇔ ⟩ ×-idˡ)
                ⟨ trans-⇔ ⟩ cong-⇔ (Fin m ⊎_) swap-×
                ⟨ trans-⇔ ⟩ cong-⇔ (Fin m ⊎_) (fin-× {n = n} {m = m})
                ⟨ trans-⇔ ⟩ fin-+ {n = m} {m = n ℕ.* m}
