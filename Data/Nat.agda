{-# OPTIONS --safe #-}

module Data.Nat where

open import Agda.Builtin.Nat using (suc; zero) renaming (Nat to ℕ) public

open import Literals.Number
open import Data.Unit

instance
  numberNat : Number ℕ
  numberNat = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → n
    }

open import Data.Bool

open import Agda.Builtin.Nat using (mod-helper; div-helper; _==_)

--           n mod (suc m) = mod-helper 0 m n m
-- n mod 2 = n mod (suc 1) = mod-helper 0 1 n 1


even : ℕ → Bool
even n = mod-helper 0 1 n 1 == 0

odd : ℕ → Bool
odd n = ! (even n)

div2 : ℕ → ℕ
div2 n = div-helper 0 1 n 1
