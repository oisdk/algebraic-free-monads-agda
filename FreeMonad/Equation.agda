{-# OPTIONS --safe #-}

open import Prelude
open import Data.Vec
open import Signatures
open import FinitenessConditions

--------------------------------------------------------------------------------
-- Equations
--------------------------------------------------------------------------------

module FreeMonad.Equation where

open import FreeMonad.Syntax
private variable 𝔽 : Signature

infix 4 _≐_
record Equation (𝔽 : Signature) (ν : Type a) : Type a
record Equation 𝔽 ν where
  constructor _≐_
  field lhs rhs : Syntax 𝔽 ν

--------------------------------------------------------------------------------
-- Algebras can "respect" an equation
--------------------------------------------------------------------------------

  infix 3 RespectedBy
  RespectedBy : 𝔽 -Alg[ B ] → Type _
  RespectedBy ϕ = ∀ ρ → interp 𝔽 ϕ ρ lhs ≡ interp 𝔽 ϕ ρ rhs

  syntax RespectedBy E ϕ = ϕ Respects E

open Equation public

--------------------------------------------------------------------------------
-- Some helper functions for more easily writing equations
--------------------------------------------------------------------------------

∀[_] : ∀ n → (∀ {A : Type} → Curryⁿ n (Syntax 𝔽 A) (const (Equation 𝔽 A))) 
   → Equation 𝔽 (Fin n)
∀[ n ] f = uncurryⁿ {A = Syntax _ (Fin n)} f var

∀ⁿ : ∀ {n} → (∀ {A : Type} → Curryⁿ n (Syntax 𝔽 A) (const (Equation 𝔽 A))) 
   → Equation 𝔽 (Fin n)
∀ⁿ {n = n} = ∀[ n ]
