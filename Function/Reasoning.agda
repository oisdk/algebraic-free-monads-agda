{-# OPTIONS --safe #-}

module Function.Reasoning where

open import Level

infixl 0 ⇒⟨∙⟩-syntax
⇒⟨∙⟩-syntax : {A : Type a} (B : Type b) → A → (A → B) → B
⇒⟨∙⟩-syntax _ x f = f x

syntax ⇒⟨∙⟩-syntax A x f = x ⇒⟨ f ⟩ A

infixl 0 ⇒⟨⟩-syntax
⇒⟨⟩-syntax : (A : Type a) → A → A
⇒⟨⟩-syntax _ x = x

syntax ⇒⟨⟩-syntax A x = x ⇒⟨⟩ A

-- private module Examples where
--   open import Prelude
--   example : (x y : ℕ) → x ≡ y → suc (suc x) ≡ ℕ.suc (suc y)
--   example x y p =
--     p ⦂ x ≡ y                   ⇒⟨ cong suc ⟩
--     suc x ≡ suc y               ⇒⟨ cong suc ⟩
--     suc (suc x) ≡ suc (suc y)   ⇒⟨⟩
--     suc (suc x) ≡ suc (suc y)
