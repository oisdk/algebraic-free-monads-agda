{-# OPTIONS --safe #-}

open import Prelude
open import Signatures
open import FinitenessConditions
open import FreeMonad.PackagedTheory

module Hoare.Boolean {ℓ} (𝒯 : FullTheory ℓ) where

open import FreeMonad.Quotiented 𝒯

open import Truth

ℋ : Term (A × Bool) → Type _
ℋ p = map₂ (const true) <$> p ≡ p

module _
  {A : Type a} (p : Term A) (ϕ : A → Bool)
  (f g : A → Term C)
  (k : (x : A) → T (ϕ x) → f x ≡ g x)
  (G : ℋ (id ▵ ϕ <$> p))
  where

  ℋ▵ : (_, true) <$> p ≡ (id ▵ ϕ) <$> p
  ℋ▵ = (λ x → x , true) <$> p ≡˘⟨ assoc p (return ∘ (id ▵ ϕ)) (return ∘ map₂ (const true)) ⟩
       map₂ (const true) <$> ((id ▵ ϕ) <$> p) ≡⟨ G ⟩
       (id ▵ ϕ) <$> p ∎

  ℋb : (k′ : A → Bool → Term B) → p >>= (λ x → k′ x true) ≡ p >>= (λ x → k′ x (ϕ x))
  ℋb k′ = sym (assoc p (return ∘ (_, true)) (uncurry k′)) ⨾ cong (_>>= uncurry k′) ℋ▵ ⨾ assoc p (return ∘ (id ▵ ϕ)) (uncurry k′)
  
  ℋ-elim : p >>= f ≡ p >>= g
  ℋ-elim =
    ℋb
      (λ x b → if b then f x else g x) ⨾ 
      (x ⇐ p ⨾/ bool {P = λ r → r ≡ ϕ x → (if r then f x else g x) ≡ g x} (const refl) (λ r → k x (subst T r tt)) (ϕ x) refl)
