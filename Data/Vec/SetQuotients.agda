{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Quotients over vectors.
--
-- One of the main tricks in order to implement free monad quotients is lifting
-- set quotients over vectors.
--
-- If we have a function
--
--   A → Syntax B / _~ₜ_
--
-- In order to implement bind, we might want a way to change that to:
--
--   (A → Syntax B) / _~_
--
-- This isn't usually possible, but we can restrict the parameters a little to
-- allow it.
--
--   Finite A ⟹ ∃ n × A ≃ Fin n
--
--   Fin n → (Syntax B / _∼ₜ_)
--            ≃
--    Vec (Syntax B / _~ₜ_) n
--
-- We can traverse over this vector to extract the quotient.
--------------------------------------------------------------------------------

open import Prelude
open import Data.Vec
open import FinitenessConditions

module Data.Vec.SetQuotients where

private
  variable
    n m : ℕ
    _~_ : A → A → Type b

open SplitQuotientedChoiceAt

--------------------------------------------------------------------------------
-- A relation on the contents of a vector can be lifted to a relation on the
-- vector itself. Here we add reflexivity to the underlying relation, which is
-- necessary to implement traverse below.
--------------------------------------------------------------------------------

module FinInst where
  infixr 5 _◂~_
  _◂~_ : A / _~_ → Vec A n / Pointwise _~_ → Vec A (suc n) / Pointwise _~_
  _◂~_ =
    rec2/
      squash/
      (λ x xs → [ x ◂ xs ])
      (λ x y xs p → eq/ _ _  λ { zero → eq/ x y p ; (suc i) → refl })
      λ x ys zs p → eq/ _ _ λ { zero → refl ; (suc i) → p i}

  finTrav : Vec (A / _~_) n → Vec A n / Pointwise _~_
  finTrav {A = A} {_~_ = _~_} {n = n} = vec-foldr (λ n → Vec _ n / Pointwise _~_) _◂~_  [ ⟅⟆ ]

  fin-SplitQuotientedChoice : SplitQuotientedChoice (Fin n) b c
  fin-SplitQuotientedChoice {B = A} {_~_} .undistrib xs = finTrav xs , funExt (lemma xs)
    where
    lemma : (x : Vec (A / _~_) n) (i : Fin n) → dist (finTrav x) i ≡ x i
    lemma {n = (suc _)} x zero    = 
      elimProp2/
        {P = λ xz xs → xz ≡ x zero → dist  (xz ◂~ xs) zero ≡ x zero }
        (λ _ _ → isProp→ (squash/ _ _))
        (λ xz xs xzp → xzp)
        (x zero)
        (finTrav (x ∘ suc))
        refl 
    lemma {n = (suc _)} x (suc i) =
      elimProp2/
        {P = λ xz xs → xs ≡ finTrav (x ∘ suc) → dist  (xz ◂~ xs) (suc i) ≡ x (suc i) }
        (λ _ _ → isProp→ (squash/ _ _))
        (λ xz xs xsp → cong (λ k → dist  k i) xsp ⨾ lemma (x ∘ suc) i)
        (x zero)
        (finTrav (x ∘ suc))
        refl 
open FinInst using (fin-SplitQuotientedChoice) public
