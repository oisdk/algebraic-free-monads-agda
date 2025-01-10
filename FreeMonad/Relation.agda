{-# OPTIONS --safe #-}

open import Prelude
open import Signatures
open import Cubical.Relation.Binary

import FreeMonad.Theory

--------------------------------------------------------------------------------
-- A Free monad, which is the syntax type quotiented by a theory
--------------------------------------------------------------------------------

module FreeMonad.Relation {ℓ}
  (𝔽 : Signature)
  (𝒯 : FreeMonad.Theory.Theory ℓ 𝔽) where


open Signature 𝔽
open import FreeMonad.Syntax 𝔽

open import FreeMonad.Theory ℓ 𝔽 hiding (ν)
open Theory 𝒯 using (Laws;Eqns)

private variable x y z : Syntax A
private
  variable
    ν : Type a
    𝒞 : Type c

open SyntaxBind

--------------------------------------------------------------------------------
-- The equivalence relation on syntax generated from a theory
------------------------------------------------------------------------------
module _ {A : Type a} where
  infix 4 _~ₜ_
  data _~ₜ_ : Syntax A → Syntax A → Type (ℓ ℓ⊔ a) where
    reflₜ   : x ≡ y → x ~ₜ y
    symₜ    : x ~ₜ y → y ~ₜ x
    transₜ  : x ~ₜ y → y ~ₜ z → x ~ₜ z
    congₜ   :  ∀ Oᵢ (kₗ kᵣ : Arity Oᵢ → Syntax A) →  (∀ i → kₗ i ~ₜ kᵣ i)
               → op (Oᵢ , kₗ) ~ₜ op (Oᵢ , kᵣ)
    eqₜ     :  ∀ i γ ρ → let lhs ≐ rhs = Eqns i .eqn γ in lhs >>= ρ ~ₜ rhs >>= ρ
    truncₜ  : (eq₁ eq₂ : x ~ₜ y) → eq₁ ≡ eq₂

Term : Type a → Type _
Term ν = Syntax ν / _~ₜ_

[_]ₜ : Syntax A → Term A
[_]ₜ = [_]

--------------------------------------------------------------------------------
-- The relation is an equivalence
--------------------------------------------------------------------------------

~ₜ-equiv : BinaryRelation.isEquivRel (_~ₜ_ {A = A})
~ₜ-equiv .BinaryRelation.isEquivRel.reflexive _ = reflₜ refl
~ₜ-equiv .BinaryRelation.isEquivRel.symmetric _ _ = symₜ
~ₜ-equiv .BinaryRelation.isEquivRel.transitive _ _ _ = transₜ

--------------------------------------------------------------------------------
-- The quotient is effective
--------------------------------------------------------------------------------

~ₜ-effective : (x y : Syntax A) → [ x ] ≡ [ y ] → x ~ₜ y
~ₜ-effective = effective/ (λ _ _ → truncₜ) ~ₜ-equiv

--------------------------------------------------------------------------------
-- Smart constructor for law
--------------------------------------------------------------------------------

lawₜ : ∀ i g  →
       let lhs ≐ rhs = Eqns i .eqn g in lhs ~ₜ rhs
lawₜ i g = let lhs ≐ rhs = Eqns i .eqn g in
  reflₜ (sym (interp-id lhs))   ⟨ transₜ ⟩
  eqₜ i g var ⟨ transₜ ⟩
  reflₜ (interp-id rhs)

--------------------------------------------------------------------------------
-- We can define a interp on the quotiented type, as long as the algebra
-- respects the theory.
--------------------------------------------------------------------------------

module _ (ϕ : 𝔽 -Alg[ B ]) (ρ : A → B) (m : ϕ Models 𝒯) (set : isSet B) where
  interpₜ-cong  : ∀ {x y : Syntax A} →  x ~ₜ y →  interp ϕ ρ x ≡ interp ϕ ρ y
  interpₜ-cong (reflₜ p)          = cong (interp ϕ ρ) p
  interpₜ-cong (symₜ p)           = sym (interpₜ-cong p)
  interpₜ-cong (transₜ x~z z~y)   = interpₜ-cong x~z ⨾ interpₜ-cong z~y
  interpₜ-cong (congₜ Oᵢ k k′ p)  = cong ϕ (cong (Oᵢ ,_) (funExt (λ i → interpₜ-cong (p i))))
  interpₜ-cong (eqₜ i γ k) = let lhs ≐ rhs = Eqns i .eqn γ in
    interp ϕ ρ (interp op k lhs)       ≡⟨ interp-comp ϕ ρ k lhs ⟩
    interp ϕ (interp ϕ ρ ∘ k) lhs      ≡⟨ m i γ (interp ϕ ρ ∘ k) ⟩
    interp ϕ (interp ϕ ρ ∘ k) rhs      ≡˘⟨ interp-comp ϕ ρ k rhs ⟩
    interp ϕ ρ (interp op k rhs)       ∎
  interpₜ-cong {x} {y} (truncₜ p q i) =  set  (interp ϕ ρ x) (interp ϕ ρ y) (interpₜ-cong p) (interpₜ-cong q) i

interpₜ : (ϕ : 𝔽 -Alg[ 𝒞 ]) (ρ : ν → 𝒞) → ϕ Models 𝒯 → isSet 𝒞 → Term ν → 𝒞
interpₜ ϕ ρ resp set = rec/ set (interp ϕ ρ) (λ _ _ → interpₜ-cong ϕ ρ resp set)

open SyntaxBind

>>=-cong : (f : A → Syntax B) → {xs ys : Syntax A} → xs ~ₜ ys → (xs >>= f) ~ₜ (ys >>= f)
>>=-cong f (reflₜ x) = reflₜ (cong (_>>= f) x)
>>=-cong f (symₜ p) = symₜ (>>=-cong f p)
>>=-cong f (transₜ p q) = transₜ (>>=-cong f p) (>>=-cong f q)
>>=-cong f (truncₜ p q i) = truncₜ (>>=-cong f p) (>>=-cong f q) i
>>=-cong f (congₜ Oᵢ kₗ kᵣ x) = congₜ Oᵢ (kₗ >=> f) (kᵣ >=> f) λ i → >>=-cong f (x i)
>>=-cong f (eqₜ i Γ k) =
  reflₜ (interp-comp op _ _ (Eqns i .eqn Γ .lhs)) ⟨ transₜ ⟩ eqₜ i Γ (k >=> f) ⟨ transₜ ⟩ reflₜ (sym (interp-comp op _ _ (Eqns i .eqn Γ .rhs)))

<$>-cong : (f : A → B) {xs ys : Syntax A} → xs ~ₜ ys → (f <$> xs) ~ₜ (f <$> ys)
<$>-cong f = >>=-cong (var ∘ f)

<$>-just-injective : (xs ys : Syntax A) → just <$> xs ~ₜ just <$> ys → xs ~ₜ ys
<$>-just-injective xs ys p =
  reflₜ (sym (interp-id xs) ⨾ sym (interp-comp op (maybe xs var) (var ∘ just) xs)) ⟨ transₜ ⟩
  >>=-cong (maybe xs var) p ⟨ transₜ ⟩
  reflₜ (interp-comp op (maybe xs var) (var ∘ just) ys ⨾ interp-id ys)
