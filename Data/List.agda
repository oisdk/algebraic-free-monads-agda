{-# OPTIONS --safe #-}

module Data.List where

open import Agda.Builtin.List
  using (List; []; _∷_)
  public

open import Cubical.Data.List.Properties using (isOfHLevelList) public
open import Level

private
  variable
    y : A
    xs : List A

foldr : (A → B → B) → B → List A → B
foldr f b []       = b
foldr f b (x ∷ xs) = f x (foldr f b xs)

para : (A → List A → B → B) → B → List A → B
para f b []       = b
para f b (x ∷ xs) = f x xs (para f b xs)

open import Data.Nat

length : List A → ℕ
length = foldr (λ _ → suc) zero

open import Data.Bool

null : List A → Bool
null = foldr (λ _ _ → false) true

open import Data.Fin

infixl 6 _!!_
_!!_ : (xs : List A) → Fin (length xs) → A
(x ∷ xs) !! suc n = xs !! n
(x ∷ xs) !! zero = x

private variable n : ℕ

tabulate : (Fin n → A) → List A
tabulate {n = zero} f = []
tabulate {n = suc n} f = f zero ∷ tabulate (λ i → f (suc i))

open import Data.Maybe

infixl 6 _!?_
_!?_ : (xs : List A) → ℕ → Maybe A
[]       !? n     = nothing
(x ∷ xs) !? zero  = just x
(x ∷ xs) !? suc n = xs !? n

open import Data.Sigma

open import Function

infixr 5 _++_
_++_ : List A → List A → List A
_++_ = flip (foldr _∷_)

mapl : (A → B) → List A → List B
mapl f = foldr (_∷_ ∘ f) []

concatMap : (A → List B) → List A → List B
concatMap f = foldr (_++_ ∘ f) []

module ListMonad where
  _>>=_ : List A → (A → List B) → List B
  _>>=_ = flip concatMap

  return : A → List A
  return x = x ∷ []

open import Decidable
open import Data.Bool
open import Path
open import Data.Unit

module DiscreteList (_≟_ : Discrete A) where
  _≡ᴮ_ : List A → List A → Bool
  [] ≡ᴮ [] = true
  [] ≡ᴮ (_ ∷ _) = false
  (_ ∷ _) ≡ᴮ [] = false
  (x ∷ xs) ≡ᴮ (y ∷ ys) = does (x ≟ y) && xs ≡ᴮ ys

  sound : (x y : List A) → T (x ≡ᴮ y) → x ≡ y
  sound [] [] ps = refl
  sound (x ∷ xs) (y ∷ ys) ps with x ≟ y
  ... | yes p = cong₂ _∷_ p (sound xs ys ps)

  complete : (x : List A) → T (x ≡ᴮ x)
  complete [] = tt
  complete (x ∷ xs) with x ≟ x
  ... | yes p = complete xs
  ... | no ¬p = ¬p refl

discreteList : Discrete A → Discrete (List A)
discreteList eq = from-bool-eq record { DiscreteList eq }

tail : List A → List A
tail (_ ∷ xs) = xs
tail []       = []

uncons : List A → Maybe (A × List A)
uncons [] = nothing
uncons (x ∷ xs) = just (x , xs)

++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++[] : (xs : List A) → xs ++ [] ≡ xs
++[] [] = refl
++[] (x ∷ xs) = cong (x ∷_) (++[] xs)
