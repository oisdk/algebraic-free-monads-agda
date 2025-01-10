{-# OPTIONS --safe #-}

open import Prelude
open import FreeMonad.PackagedTheory
open import Signatures
open import FinitenessConditions

module FreeMonad.Combinations.Sum
  {ℓ}
  (T₁ : FullTheory ℓ)
  (T₂ : FullTheory ℓ)
  where

open FullTheory T₁ renaming (𝒯 to 𝒯₁; finiteArity to finAr₁; finiteVars to finVar₁)
open FullTheory T₂ renaming (𝔽 to 𝔾; 𝒯 to 𝒯₂; finiteArity to finAr₂; finiteVars to finVar₂)

open Signature

open import FreeMonad.Theory
open import FreeMonad.Syntax

open Theory

import FreeMonad.Quotiented

module F₁ = FreeMonad.Quotiented T₁
module F₂ = FreeMonad.Quotiented T₂

inj₁ : Syntax 𝔽 A → Syntax (𝔽 ⊞ 𝔾) A
inj₁ = interp _ (op ∘ inl-map) var

inj₂ : Syntax 𝔾 A → Syntax (𝔽 ⊞ 𝔾) A
inj₂ = interp _ (op ∘ inr-map) var

law₁ : Law ℓ 𝔽 → Law ℓ (𝔽 ⊞ 𝔾)
law₁ law .Γ = _
law₁ law .ν = _
law₁ law .eqn i = let lhs ≐ rhs = law .eqn i in inj₁ lhs ≐ inj₁ rhs

law₂ : Law ℓ 𝔾 → Law ℓ (𝔽 ⊞ 𝔾)
law₂ law .Γ = _
law₂ law .ν = _
law₂ law .eqn γ = let lhs ≐ rhs = law .eqn γ in inj₂ lhs ≐ inj₂ rhs

𝒯 : Theory ℓ (𝔽 ⊞ 𝔾)
𝒯 .Laws = 𝒯₁ .Laws ⊎ 𝒯₂ .Laws
𝒯 .Eqns = either (law₁ ∘ 𝒯₁ .Eqns) (law₂ ∘ 𝒯₂ .Eqns)

finArity : ∀ Oᵢ → SplitQuotientedChoiceω (Arity (𝔽 ⊞ 𝔾) Oᵢ)
finArity (inl x) = finAr₁ x
finArity (inr x) = finAr₂ x

finVars : FiniteVars 𝒯
finVars (inl x) = finVar₁ x
finVars (inr x) = finVar₂ x

combinedTheory : FullTheory ℓ
combinedTheory .FullTheory.𝔽 = 𝔽 ⊞ 𝔾
combinedTheory .FullTheory.𝒯 = 𝒯
combinedTheory .FullTheory.finiteArity = finArity
combinedTheory .FullTheory.finiteVars = finVars

interp₁ : (f : 𝔽 -Alg[ B ]) (g : 𝔾 -Alg[ B ]) (k : A → B)
        → (xs : Syntax 𝔽 A)
        → interp _ (f -⊞- g) k (inj₁ xs) ≡ interp _ f k xs
interp₁ f g k (var x) = refl
interp₁ f g k (op (O , xs)) = cong (f ∘ _,_ O) (funExt λ i → interp₁ f g k (xs i))

interp₂ : (f : 𝔽 -Alg[ B ]) (g : 𝔾 -Alg[ B ]) (k : A → B)
        → (xs : Syntax 𝔾 A)
        → interp _ (f -⊞- g) k (inj₂ xs) ≡ interp _ g k xs
interp₂ f g k (var x) = refl
interp₂ f g k (op (O , xs)) = cong (g ∘ _,_ O) (funExt λ i → interp₂ f g k (xs i))

inj₁-com : (f : (𝔽 ⊞ 𝔾) -Alg[ B ]) (k : A → B) (xs : Syntax 𝔽 A) →
          interp _ (f ∘ inl-map) k xs ≡ interp _ f k (inj₁ xs)
inj₁-com f k (FreeMonad.Syntax.var x) = refl
inj₁-com f k (FreeMonad.Syntax.op (O , xs)) = cong (f ∘ _,_ (inl O)) (funExt λ i → inj₁-com f k (xs i))

inj₂-com : (f : (𝔽 ⊞ 𝔾) -Alg[ B ]) (k : A → B) (xs : Syntax 𝔾 A) →
          interp _ (f ∘ inr-map) k xs ≡ interp _ f k (inj₂ xs)
inj₂-com f k (var x) = refl
inj₂-com f k (op (O , xs)) = cong (f ∘ _,_ (inr O)) (funExt λ i → inj₂-com f k (xs i))

open FreeMonad.Quotiented combinedTheory

lift₁ : F₁.Term A → Term A
lift₁ = F₁.interpₜ (opₜ ∘ inl-map) return resp squash/
  where
  resp : (opₜ ∘ inl-map) Models 𝒯₁
  resp i t k =
    let lhs ≐ rhs = Theory.Eqns 𝒯₁ i .eqn t
    in interp _ (opₜ ∘ inl-map) k lhs ≡⟨ inj₁-com opₜ k lhs ⟩
          interp _ opₜ k (inj₁ lhs) ≡⟨ opₜ-resp (inl i) t k ⟩
          interp _ opₜ k (inj₁ rhs) ≡˘⟨ inj₁-com opₜ k rhs ⟩
       interp _ (opₜ ∘ inl-map) k rhs ∎

⊞-resp : (ϕ : 𝔽 -Alg[ A ]) (ψ : 𝔾 -Alg[ A ])
       → ϕ Models 𝒯₁
       → ψ Models 𝒯₂
       → (ϕ -⊞- ψ) Models 𝒯
⊞-resp ϕ ψ resp₁ resp₂ (inl i) t k = let lhs ≐ rhs = Theory.Eqns 𝒯₁ i .eqn t in interp₁ ϕ ψ k lhs ⨾ resp₁ i t k ⨾ sym (interp₁ ϕ ψ k rhs)
⊞-resp ϕ ψ resp₁ resp₂ (inr i) t k = let lhs ≐ rhs = Theory.Eqns 𝒯₂ i .eqn t in interp₂ ϕ ψ k lhs ⨾ resp₂ i t k ⨾ sym (interp₂ ϕ ψ k rhs)

module _ {A : Type a} where
  lift₂-alg : 𝔾 -Alg[ Term A ]
  lift₂-alg = opₜ ∘ inr-map

  lift₂-resp : lift₂-alg Models 𝒯₂
  lift₂-resp i t k =
    let lhs ≐ rhs = Theory.Eqns 𝒯₂ i .eqn t
    in interp _ (opₜ ∘ inr-map) k lhs ≡⟨ inj₂-com opₜ k lhs ⟩
          interp _ opₜ k (inj₂ lhs) ≡⟨ opₜ-resp (inr i) t k ⟩
          interp _ opₜ k (inj₂ rhs) ≡˘⟨ inj₂-com opₜ k rhs ⟩
      interp _ (opₜ ∘ inr-map) k rhs ∎

  lift₂ : F₂.Term A → Term A
  lift₂ = F₂.interpₜ lift₂-alg return lift₂-resp squash/
