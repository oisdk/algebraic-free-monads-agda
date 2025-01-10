{-# OPTIONS --safe --lossy-unification #-}

open import Prelude renaming (tt to ⟨⟩)
open import Signatures
open import FinitenessConditions
open import FreeMonad.PackagedTheory

-- This could all be redefined to work over a generic monad (instead of Term),
-- but unfortunately that takes extremely long to typecheck. I'm going to
-- proceed with this slightly specialised version, and maybe switch out the
-- definitions later.
--
-- Also: the universe polymorphism here is making things crazy slow. If
-- you miss a single application it can blow up the typechecking time to several
-- hours (rather then ~10 seconds). I plan to remove it in some principled way
-- (i.e. replace all the levels with one)

module Hoare.Definition {ℓ} (𝒯 : FullTheory ℓ) where

open import FreeMonad.Quotiented 𝒯

-- open import Truth hiding (Ω; True)

[_/⟨⟩] : Term A → Term ⊤
[_/⟨⟩] = _>> return ⟨⟩

module _ (p : Level) where
  module _ {A : Type a} where
    SEF : Term A → Type _
    SEF t = ∀ {R : Type p} (k : Term R) → (do t ; k) ≡ k

    DET : Term A → Type _
    DET t = ∀ {R : Type p} (k : A → A → Term R) → (do x ← t ; y ← t ; k x y) ≡ (do x ← t ; t ; k x x)


module _ (p : Level) where
  open import Truth.Definition p

  Assertion : Type (ℓ ℓ⊔ ℓsuc (ℓsuc p))
  Assertion = Σ[ ϕ ⦂ Term Ω ] × SEF (ℓsuc p) ϕ × DET (ℓsuc p) ϕ

-- We need to keep the variables in the expression. This is a difference from
-- HasCasl.

open import Truth

module _ {A : Type a} {b c : Level} where
  record Hoare (ϕ : Term (Ω b)) (t : Term A) (ψ : A → Term (Ω c)) : Type (ℓ ℓ⊔ ℓsuc (a ℓ⊔ ℓsuc (b ℓ⊔ c))) where
    no-eta-equality
    field
      proof : ∀ {R : Type (a ℓ⊔ ℓsuc (b ℓ⊔ c))} → (k : A → Ω (b ℓ⊔ c) → Term R) →
        (do a ← ϕ
            x ← t
            b ← ψ x
            k x (a |→| b)) ≡

        (do a ← ϕ
            x ← t
            b ← ψ x
            k x True)

    on-pair : 
        (do a ← ϕ
            x ← t
            b ← ψ x
            return (x , a |→| b)) ≡
        (do a ← ϕ
            x ← t
            b ← ψ x
            return (x , True))
    on-pair = proof λ x p → return (x , p)
  open Hoare public

  syntax Hoare ϕ p (λ x → ψ) = ⟅ ϕ ⟆ x ← p ⟅ ψ ⟆

Hoare-NoVar : Term (Ω b) → Term A → Term (Ω c) → Type _
Hoare-NoVar ϕ p ψ = Hoare ϕ p (const ψ)

syntax Hoare-NoVar ϕ p ψ = ⟅ ϕ ⟆ p ⟅ ψ ⟆

Hoare-NoAssume : {A : Type a} → Term A → (A → Term (Ω b)) → Type _
Hoare-NoAssume p ψ = Hoare (return (True {ℓzero})) p ψ

syntax Hoare-NoAssume p (λ x → ψ) = ⟅⟆ x ← p ⟅ ψ ⟆

Hoare-NoAssumeNoVar : Term ⊤ → Term (Ω b) → Type _
Hoare-NoAssumeNoVar = Hoare-NoVar (return (True {ℓzero}))

syntax Hoare-NoAssumeNoVar p ψ = ⟅⟆ p ⟅ ψ ⟆
