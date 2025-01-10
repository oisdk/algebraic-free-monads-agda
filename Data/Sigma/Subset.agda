{-# OPTIONS --safe #-}

module Data.Sigma.Subset where

open import Prelude

Subset : (A : Type a) (P : A → Type p) → Type (a ℓ⊔ p)
Subset A P = Σ[ x ⦂ A ] × ∥ P x ∥

Subset/ : (A : Type a) (P : A → Type p) → Type (a ℓ⊔ p)
Subset/ A P = (Σ[ x ⦂ A ] × P x) / λ x y → fst x ≡ fst y

subset-quot : Subset A P → Subset/ A P
subset-quot (x , ∥Px∥) = ∥rec∥→Set squash/ (λ Px → [ x , Px ]) (λ Px₁ Px₂ → eq/ (x , Px₁) (x , Px₂) refl) ∥Px∥

module _ (set : isSet A) where
  subset-iso : Subset A P ⇔ Subset/ A P
  subset-iso .fun = subset-quot
  subset-iso .inv = rec/ (isSetΣ set λ _ → isProp→isSet squash) (map₂ ∣_∣) λ _ _ → Σ≡Prop λ _ → squash 
  subset-iso .rightInv = elimProp/ (λ _ → squash/ _ _) (λ _ → refl)
  subset-iso .leftInv (x , Px) =
    ∥elim∥
      {P = λ Px → subset-iso .inv (subset-quot (x , Px)) ≡ (x , Px)}
      (λ _ → λ p q → isSetΣ set (λ _ → isProp→isSet squash) _ _ p q )
      (λ _ → refl)
      Px
