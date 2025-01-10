{-# OPTIONS --safe #-}

module Path.Reasoning where

open import Level
open import Path

infixr 2 ≡˘⟨⟩-syntax _≡⟨⟩_ ≡⟨∙⟩-syntax ≡⟨∙⟩[∙]-syntax ≡⟨↦⟩-syntax

≡˘⟨⟩-syntax : ∀ (x : A) {y z} → y ≡ z → y ≡ x → x ≡ z
≡˘⟨⟩-syntax _ y≡z y≡x = sym y≡x ⨾ y≡z

syntax ≡˘⟨⟩-syntax x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

≡⟨∙⟩-syntax : ∀ (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨∙⟩-syntax _ y≡z x≡y = x≡y ⨾ y≡z

syntax ≡⟨∙⟩-syntax x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

≡⟨↦⟩-syntax : ∀ (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨↦⟩-syntax = ≡⟨∙⟩-syntax

syntax ≡⟨↦⟩-syntax x y≡z (λ i → x≡y) = x ≡⟨ i ↦ x≡y ⟩ y≡z

_≡⟨⟩_ : ∀ (x : A) {y} → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

infix 2.5 _∎
_∎ : ∀ {A : Type a} (x : A) → x ≡ x
_∎ x = refl

≡⟨∙⟩[∙]-syntax : ∀ (x : A) {x′ y′ : B} {y z} → y ≡ z → x′ ≡ y′ → (x′ ≡ y′ → x ≡ y) → x ≡ z
≡⟨∙⟩[∙]-syntax _ y≡z x′≡y′ x′≡y′⇒x≡y = x′≡y′⇒x≡y x′≡y′ ⨾ y≡z

syntax ≡⟨∙⟩[∙]-syntax x y≡z x′≡y′ x′≡y′⇒x≡y = x ≡⟨ x′≡y′⇒x≡y ⟩[ x′≡y′ ] y≡z

infixr 2 begin[_]_
begin[_]_ : {x y : A} → I → x ≡ y → A
begin[ i ] p = p i
