{-# OPTIONS --safe #-}

open import Prelude
open import Data.Vec
open import Signatures
open import Cubical.Relation.Binary
open import FinitenessConditions
open import FreeMonad.PackagedTheory

module FreeMonad.Modalities {ℓ} (theory : FullTheory ℓ) where

open FullTheory theory
open import FreeMonad.Quotiented theory
open Signature 𝔽
open import FreeMonad.Syntax 𝔽 renaming (var to varₛ)
open import FreeMonad.Theory ℓ 𝔽

private variable xs ys zs : Syntax A

□ₛ : (A → Type p) → Syntax A → Type p
□ₛ P = interp (λ { (O , xs) → ∀ i → xs i }) P

◇ₛ : (A → Type p) → Syntax A → Type p
◇ₛ P = interp (λ { (O , xs) → ∃ i × xs i }) P

mutual
  □ₛₚ : (Syntax A → Type p) → Syntax A → Type p
  □ₛₚ P xs = P xs × □ₛₚ′ P xs

  □ₛₚ′ : (Syntax A → Type p) → Syntax A → Type p
  □ₛₚ′ P (varₛ x) = Poly-⊤
  □ₛₚ′ P (op (o , k)) = ∀ i → □ₛₚ P (k i)

□ₜ : (A → Type p) → Term A → Type _
□ₜ P xs = ∃ ys × [ ys ] ≡ xs × □ₛ P ys

□ₚ : (Syntax A → Type p) → Term A → Type _
□ₚ P t = ∃ s × [ s ] ≡ t × □ₛₚ P s

◇ₜ : (A → Type p) → Term A → Type _
◇ₜ P xs = ∃ ys × [ ys ] ≡ xs × ◇ₛ P ys
