{-# OPTIONS --safe #-}

open import Prelude
open import Relation.Binary

module Relation.Binary.Equivalence {ℓ r} {E : Type ℓ} (_~_ : E → E → Type r) where

private variable x y z : E

data _≈_ (x y : E) : Type (ℓ ℓ⊔ r) where
  reflₑ  : x ≡ y → x ≈ y
  symₑ   : y ≈ x → x ≈ y
  transₑ : x ≈ z → z ≈ y → x ≈ y
  relₑ   : x ~ y → x ≈ y

open import Cubical.Relation.Binary

≈-isEquivRel : BinaryRelation.isEquivRel _≈_
≈-isEquivRel .isEquivRel.reflexive _ = reflₑ refl
≈-isEquivRel .isEquivRel.symmetric _ _ = symₑ
≈-isEquivRel .isEquivRel.transitive _ _ _ = transₑ

module _ {R : B → B → Type c} (f : E → B) (equivRel : isEquivRel R) (ϕ : ∀ {x y} → x ~ y → R (f x) (f y)) where
  open isEquivRel equivRel

  ≈-rec : x ≈ y → R (f x) (f y)
  ≈-rec (reflₑ x) = subst (R _) (cong f x) (reflexive _)
  ≈-rec (symₑ y≈x) = symmetric  _ _ (≈-rec y≈x)
  ≈-rec (transₑ x≈z z≈y) = transitive _ _ _ (≈-rec x≈z) (≈-rec z≈y)
  ≈-rec (relₑ x~y) = ϕ x~y

≈-rec-≡ : (f : E → B) → (∀ {x y} → x ~ y → f x ≡ f y) → ∀ {x y} → x ≈ y → f x ≡ f y
≈-rec-≡ f = ≈-rec f ≡-isEquivRel

_≋_ : E → E → Type (ℓ ℓ⊔ r)
x ≋ y = ∥ x ≈ y ∥

≋-isEquivRel : isEquivRel _≋_
≋-isEquivRel .isEquivRel.reflexive _ = ∣ reflₑ refl ∣
≋-isEquivRel .isEquivRel.symmetric _ _ = ∥rec∥ squash (∣_∣ ∘ symₑ)
≋-isEquivRel .isEquivRel.transitive _ _ _ = ∥rec2∥ squash λ x y → ∣ transₑ x y ∣

module _ {R : B → B → Type c} (f : E → B) (equivRel : isEquivRel R) (isPropR : ∀ {x y} → isProp (R (f x) (f y))) (ϕ : ∀ {x y} → x ~ y → R (f x) (f y)) where
  ≋-rec : x ≋ y → R (f x) (f y)
  ≋-rec = ∥rec∥ isPropR (≈-rec f equivRel ϕ)

≋-rec-≡ : (f : E → B) → isSet B → (∀ {x y} → x ~ y → f x ≡ f y) → x ≋ y → f x ≡ f y
≋-rec-≡ f set ϕ = ≋-rec f ≡-isEquivRel (set _ _) ϕ

open import Cubical.Foundations.Isomorphism using (isProp→Iso)

module _ {x y : E} where
  ≋⇔quot : Path (E / _~_) [ x ] [ y ] ⇔ (x ≋ y)
  ≋⇔quot =
    isProp→Iso (squash/ [ x ] [ y ]) (squash/ [ x ] [ y ])
      (cong (rec/ squash/ [_] (λ x y r → eq/ x y ∣ relₑ r ∣)))
      (cong (rec/ squash/ [_] λ _ _ → ≋-rec-≡ [_] squash/ (eq/ _ _)))
      ⟨ trans-⇔ ⟩
    isProp→Iso
      (squash/ [ x ] [ y ])
      squash
      (effective/ (λ _ _ → squash) ≋-isEquivRel x y)
      (eq/ x y)
