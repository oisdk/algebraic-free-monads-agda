{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Vectors implemented as functions from Fins
--------------------------------------------------------------------------------

module Data.Vec where

open import Prelude hiding (tabulate)

Vec : Type a → ℕ → Type a
Vec A n = (i : Fin n) → A

private variable n m : ℕ

infixr 5 _◂_
_◂_ : A → Vec A n → Vec A (suc n)
(x ◂ xs) zero    = x
(x ◂ xs) (suc i) = xs i

⟅⟆ : Vec A zero
⟅⟆ ()

vec-foldr : (N : ℕ → Type b) → 
            (∀ {n} → A → N n → N (suc n)) →
            N zero →
            Vec A n → N n
vec-foldr {n = zero}  N f b xs = b
vec-foldr {n = suc n} N f b xs = f (xs zero) (vec-foldr N f b (xs ∘ suc))

◂-id : (xs : Vec A (suc n)) → xs zero ◂ xs ∘ suc ≡ xs
◂-id xs = funExt λ { zero → refl ; (suc i) → refl }

singleton-id : (x : A) → x ◂ ⟅⟆ ≡ const x
singleton-id _ = funExt λ { zero → refl }

head-singleton-id : (xs : Vec A 1) → xs zero ◂ ⟅⟆ ≡ xs
head-singleton-id _ = funExt λ { zero → refl }

ConcreteVec : Type a → ℕ → Type a
ConcreteVec A zero    = Poly-⊤
ConcreteVec A (suc n) = A × ConcreteVec A n

tabulate : Vec A n → ConcreteVec A n
tabulate {n = zero}  xs = Poly-tt
tabulate {n = suc n} xs = xs 0 , tabulate (xs ∘ suc)

Curryⁿ : (n : ℕ) → (A : Type a) → (P : ConcreteVec A n → Type a) → Type a
Curryⁿ zero    A P = P Poly-tt
Curryⁿ (suc n) A P = (x : A) → Curryⁿ n A (P ∘ _,_ x)

uncurryⁿ : ∀ {n} {P : ConcreteVec A n → Type a} → Curryⁿ n A P → (xs : Vec A n) → P (tabulate xs)
uncurryⁿ {n = zero}  f xs = f
uncurryⁿ {n = suc n} f xs = uncurryⁿ (f (xs zero)) (xs ∘ suc)
