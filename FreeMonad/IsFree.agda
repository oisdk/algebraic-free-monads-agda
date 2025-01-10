{-# OPTIONS --safe #-}

open import Prelude
open import Signatures
open import FinitenessConditions
open import FreeMonad.PackagedTheory

module FreeMonad.IsFree (theory : FullTheory 0) where

open FullTheory theory

open Signature 𝔽
open import FreeMonad.Syntax 𝔽 renaming (var to varₛ)
open import FreeMonad.Theory
open import FreeMonad.Quotiented theory

module _ {A : Type} where
  infix 4 _≈ₜ_
  _≈ₜ_ : Syntax A → Syntax A → Type _
  t₁ ≈ₜ t₂ =  {𝒞 : Type} →
              isSet 𝒞 →
              (ϕ : 𝔽 -Alg[ 𝒞 ]) →
              ϕ Models 𝒯 → 
              ∀ ρ → interp ϕ ρ t₁ ≡ interp ϕ ρ t₂

  ≈⇒∼ : (x y : Syntax A) → x ≈ₜ y → x ~ₜ y
  ≈⇒∼ x y x≈ₜy = 
    ~ₜ-effective _ _
      ( cong [_] (sym (interp-id x))
      ⨾ interp-opₜ-com-[] varₛ x
      ⨾ x≈ₜy squash/ opₜ opₜ-resp return
      ⨾ sym (interp-opₜ-com-[] varₛ y)
      ⨾ cong [_] (interp-id y))

  ~⇒≈ : (x y : Syntax A) → x ~ₜ y → x ≈ₜ y
  ~⇒≈ x y p set ϕ t k = interpₜ-cong ϕ k t set p

private variable
  m l : Level
  ℳ : Type₁
  ℒ : Type₁

IsHom : 𝔽 -Alg[ ℳ ] → 𝔽 -Alg[ ℒ ] → (ℳ → ℒ) → Type _
IsHom ϕ ψ h = ∀ x → h (ϕ x) ≡ ψ (cmap h x)

module _
  {X : Type₁}
  (ϕ :  𝔽 -Alg[ ℒ ])
  (f : X → ℒ)
  (ϕ-resp : ϕ Models 𝒯)
  (setL : isSet ℒ)
  where

  ⟦f⟧ : Term X → ℒ
  ⟦f⟧ = interpₜ ϕ f ϕ-resp setL

  η : X → Term X
  η = return

  -- diag : f ≡ ⟦f⟧ ∘ η
  -- diag = refl

  ⟦f⟧-hom : IsHom opₜ ϕ ⟦f⟧
  ⟦f⟧-hom (Oᵢ , k) =
      SplitQuotientedChoiceAt.elim~canonical
        (finiteArity _)
        (λ k → ⟦f⟧ (opₜ (Oᵢ , k)) ≡ ϕ (cmap ⟦f⟧ (Oᵢ ,  k))) (λ _ → setL _ _ )
        (λ k → cong ⟦f⟧ (opₜ-com-[] k))
        k

  module _ (h : Term X → ℒ) (hom : IsHom opₜ ϕ h) (diag : ∀ x → h (return x) ≡ f x) where
    uniq : ∀ x → h x ≡ ⟦f⟧ x
    uniq = elimₜ-prop _ (λ _ → setL _ _) alg
      where
      alg : ∀ xs → h [⟪ xs ⟫] ≡ ⟦f⟧ [⟪ xs ⟫]
      alg (varₛ x) = diag x
      alg (op (O , k) P⟨xs⟩) = hom (O , k) ⨾ cong (ϕ ∘ (_,_ O)) (funExt P⟨xs⟩) ⨾ sym (⟦f⟧-hom (O , k))
