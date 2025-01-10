{-# OPTIONS --safe #-}

open import Prelude
  hiding (⊤; tt; Poly-⊤; Poly-tt; ⊥; Poly-⊥)

module Truth.Combinators {ℓ : Level} where

import Prelude
open import Data.Unit.UniversePolymorphic {ℓ}
open import Data.Empty.UniversePolymorphic {ℓ}
open import Truth.Definition ℓ

private
  variable X Y Z : Ω

True : Ω
ProofOf True = ⊤
IsProp  True _ _ = refl

False : Ω
ProofOf False = ⊥
IsProp  False ()

open import Cubical.Foundations.HLevels using (isPropIsOfHLevel)

cong-∥ : (x y : Ω) → (lhs : ProofOf x ≡ ProofOf y) → PathP (λ i → isProp (lhs i)) (IsProp x) (IsProp y) → x ≡ y
cong-∥ x y lhs rhs i .ProofOf = lhs i
cong-∥ x y lhs rhs i .IsProp = rhs i

Ω≡ : (x y : Ω) → ProofOf x ≡ ProofOf y → x ≡ y
Ω≡ x y p = 
  cong-∥ x y p
    (J (λ y idxy → ∀ lhs rhs → PathP (λ i → isProp (idxy i)) lhs rhs) (isPropIsOfHLevel 1) p (IsProp x) (IsProp y))

_iff_ : (ProofOf X → ProofOf Y) → (ProofOf Y → ProofOf X) → X ≡ Y
_iff_ {X = x} {Y = y} lhs rhs =
  Ω≡ x y (isoToPath (iso lhs rhs (λ _ → y .IsProp _ _) λ _ → x .IsProp _ _))

proves-lhs : (x : Ω) → ProofOf x → ProofOf x ≡ ⊤
proves-lhs x p = isoToPath (iso (const tt) (const p) (λ _ → refl) λ _ → IsProp x _ _)

proves : ProofOf X → X ≡ True
proves p = const tt iff const p

disproves :  (ProofOf X → Prelude.⊥)
        →   X ≡ False
disproves p = (absurd ∘ p) iff λ ()

at-most-two : ∄ p × p ≢ True × p ≢ False
at-most-two (p , p≢True , p≢False) = p≢False (disproves (p≢True ∘ proves))

extract : {x : Ω} → x ≡ True → ProofOf x
extract p = subst ProofOf (sym p) tt

open import Cubical.Foundations.HLevels

Truth⇔hProp : Ω ⇔ hProp ℓ
Truth⇔hProp .fun x .fst = x .ProofOf
Truth⇔hProp .fun x .snd = x .IsProp
Truth⇔hProp .inv x .ProofOf = x .fst
Truth⇔hProp .inv x .IsProp = x .snd
Truth⇔hProp .rightInv b = refl
Truth⇔hProp .leftInv x i .ProofOf = x .ProofOf
Truth⇔hProp .leftInv x i .IsProp = x .IsProp

abstract
  isSetΩ : isSet Ω
  isSetΩ = subst isSet (sym (isoToPath Truth⇔hProp)) isSetHProp
