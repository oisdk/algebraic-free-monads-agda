{-# OPTIONS --safe #-}

module HLevels where

open import Cubical.Foundations.HLevels using
  (isSetΠ; isProp→; isSet×; isPropΠ; isPropΣ; isProp×; isSetΣ; isSet→SquareP; isOfHLevelPath; isOfHLevel→isOfHLevelDep; isOfHLevelΣ; isOfHLevelΠ)
  public
open import Cubical.Foundations.Everything using
  (isProp; isSet; isContr; isOfHLevel; isProp→isSet; flipSquare)
  public
open import Cubical.Foundations.Prelude using
  (Square)
  public
open import Cubical.Foundations.Prelude

open import Level

isSet→ : isSet B → isSet (A → B)
isSet→ set = isSetΠ λ _ → set

{-
The following function fills such a degenerated cube (without two side faces) in a set:
        a ------- x -----------------  c
     /    \           /  \           /    \
    /      \         /    \         /      \
   |    σ   |       |     |        |    σ   |
  p|    ∼   |q      |     |       s|    ∼   |t
    \      /         \   /          \      /
     \    /           \ /            \    /
        b ------- y -----------------  d
-}
isSet→SimpleCube : ∀ {ℓ} {A : Type ℓ} → {a b c d : A} → isSet A →
                   (p q : a ≡ b) → (σ : p ≡ q) →
                   (s t : c ≡ d) → (τ : s ≡ t) →
                   (x : a ≡ c) → (y : b ≡ d) →
                   (f₁ : Square p s x y) →
                   (f₂ : Square q t x y) →
                   PathP (λ k → f₁ k ≡ f₂ k) σ τ
isSet→SimpleCube {ℓ} {A} {a} {b} {c} {d}
  set p q σ s t τ x y f₁ f₂ = let filler : PathP (λ k → f₁ k ≡ f₂ k) (set a b p q) (set c d s t)
                                  filler = λ k → set (x k) (y k) (f₁ k) (f₂ k)
                              in subst2 (λ S T → PathP (λ k → f₁ k ≡ f₂ k) S T)
                                   (isOfHLevelPath 1 (set a b) p q  _ σ )
                                   ((isOfHLevelPath 1 (set c d) s t  _ τ ))
                                   filler
