{-# OPTIONS --safe --lossy-unification #-}

open import Prelude renaming (tt to ⟨⟩)
open import Signatures
open import FinitenessConditions
open import FreeMonad.PackagedTheory
open import Finite using (ℰ)
open import FreeMonad.Theory using (DiscreteVars)

module Hoare.HElim (𝒯 : FullTheory ℓzero)
                   (findVar : DiscreteVars (FullTheory.𝒯 𝒯))
                   (fin-arities : ∀ Oᵢ → ℰ (Signature.Arity (FullTheory.𝔽 𝒯) Oᵢ)) where

open import Truth using (ProofOf ; _|→|_ ; |→|-idˡ; True; Ω)
open import Hoare.Definition 𝒯
open import FreeMonad.HElim 𝒯 findVar fin-arities
open import FreeMonad.Quotiented 𝒯

module _ {p : Level} where
  -- open import Truth.MonoLevel p
  -- open DisplayGlobal {p}

  -- This is just 𝒢-elim repackaged for Hoare logic
  module _ {A B : Type}
           (ϕ : A → Ω p)
           (f g : A → Term B)
           (k : (x : A) → ProofOf (ϕ x) → f x ≡ g x)
           (p : Term A) where
    H-elim  : ⟅⟆ x ← p ⟅ return (ϕ x) ⟆ → (p >>= f) ≡ (p >>= g)
    H-elim h = 𝒢-elim ϕ f g k p $
      ϕ? ϕ <$> p ≡⟨⟩
      (do x ← p; return (x , ϕ x)) ≡⟨ x ⇐ p ⨾/ cong (return ∘ (_,_ x)) (const Truth.iff λ f → f _) ⟩
      (do x ← p; return (x , True |→| ϕ x)) ≡⟨ on-pair h ⟩
      (do x ← p; return (x , True)) ≡⟨⟩
      ϕT ϕ <$> p ∎
