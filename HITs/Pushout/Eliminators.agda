{-# OPTIONS --safe #-}

open import Prelude

module HITs.Pushout.Eliminators {A : Type a} {B : Type b} {C : Type c} {f : A → B} {g : A → C} where

open import HITs.Pushout.Base f g


module _ (P : Pushout → Type p) where
  module _
    (setP : ∀ x → isSet (P x))
    (f⁻ : ∀ x → P (inl x))
    (g⁻ : ∀ x → P (inr x))
    (pull : ∀ x → PathP (λ i → P (push x i)) (f⁻ (f x)) (g⁻ (g x)))
    where
    elim : ∀ x → P x
    elim (inl x) = f⁻ x
    elim (inr x) = g⁻ x
    elim (push x i) = pull x i
    elim (trunc xs ys p q i j) =
      isOfHLevel→isOfHLevelDep
        2
        setP
        (elim xs)
        (elim ys)
        (cong elim p)
        (cong elim q)
        (trunc xs ys p q)
        i j
  module _
    (propP : ∀ x → isProp (P x))
    (f⁻ : ∀ x → P (inl x))
    (g⁻ : ∀ x → P (inr x))
    where
    elimProp : ∀ x → P x
    elimProp =
      elim
        (λ x → isProp→isSet (propP x))
        f⁻ g⁻
        λ x → isOfHLevel→isOfHLevelDep 1 propP (f⁻ (f x)) (g⁻ (g x)) (push x)

module _
  (P : Pushout → Pushout → Type p)
  (propP : ∀ x y → isProp (P x y))
  (fn : ∀ x y → P (pull x) (pull y))
  where
  elimProp2 : ∀ x y → P x y
  elimProp2 =
    elimProp _
      (λ x → isPropΠ λ y → propP x y)
      (λ x → elimProp _ (propP (inl x)) (fn (inl x) ∘′ inl) (fn (inl x) ∘′ inr))
      (λ x → elimProp _ (propP (inr x)) (fn (inr x) ∘′ inl) (fn (inr x) ∘′ inr))

module _ {d} {D : Type d} where
  rec : isSet D
      → (f⁻ : B → D)
      → (g⁻ : C → D)
      → (∀ x → f⁻ (f x) ≡ g⁻ (g x))
      → Pushout → D
  rec set = elim (λ _ → D) (λ _ → set)
