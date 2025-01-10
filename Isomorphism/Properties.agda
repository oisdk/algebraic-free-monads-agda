{-# OPTIONS --safe #-}

module Isomorphism.Properties where

open import Prelude

open import Cubical.Data.Sigma.Properties
  using ()
  renaming ( Σ-assoc-Iso to Σ-assoc
           ; Σ-swap-Iso to Σ-swap)
  public

swap-⊎ : (A ⊎ B) ⇔ (B ⊎ A)
swap-⊎ .fun = inr ▿ inl
swap-⊎ .inv = inr ▿ inl
swap-⊎ .rightInv (inl x) = refl
swap-⊎ .rightInv (inr x) = refl
swap-⊎ .leftInv (inl x) = refl
swap-⊎ .leftInv (inr x) = refl

⇔-lift : Lift {ℓ₂ = b} A ⇔ A
⇔-lift .fun = lower
⇔-lift .inv = lift
⇔-lift .rightInv _ = refl
⇔-lift .leftInv _ = refl

swap-× : (A × B) ⇔ (B × A)
swap-× = Σ-swap

Σ-idˡ : (Σ[ t ⦂ ⊤ ] × P t) ⇔ P tt
Σ-idˡ .fun = snd
Σ-idˡ .inv = tt ,_
Σ-idˡ .rightInv _ = refl
Σ-idˡ .leftInv  _ = refl

×-idˡ : (⊤ × A) ⇔ A
×-idˡ = Σ-idˡ

×-annˡ : (⊥ × A) ⇔ ⊥
×-annˡ .fun = fst
×-annˡ .inv ()
×-annˡ .rightInv ()
×-annˡ .leftInv ()

⊎-idˡ : (⊥ ⊎ A) ⇔ A
⊎-idˡ .fun = absurd ▿ id
⊎-idˡ .inv = inr
⊎-idˡ .rightInv _ = refl
⊎-idˡ .leftInv (inr x) = refl

×-distrib-⊎ : (A × (B ⊎ C)) ⇔ ((A × B) ⊎ (A × C))
×-distrib-⊎ .fun (x , y) = map-⊎ (x ,_) (x ,_) y
×-distrib-⊎ .inv = map₂ inl ▿ map₂ inr
×-distrib-⊎ .rightInv (inl x) = refl
×-distrib-⊎ .rightInv (inr x) = refl
×-distrib-⊎ .leftInv (x , inl _) = refl
×-distrib-⊎ .leftInv (x , inr _) = refl

⊎-assoc : ((A ⊎ B) ⊎ C) ⇔ (A ⊎ (B ⊎ C))
⊎-assoc .fun = (inl ▿ (inr ∘ inl)) ▿ (inr ∘ inr)
⊎-assoc .inv = (inl ∘ inl) ▿ ((inl ∘ inr) ▿ inr)
⊎-assoc .rightInv (inl x) = refl
⊎-assoc .rightInv (inr (inl x)) = refl
⊎-assoc .rightInv (inr (inr x)) = refl
⊎-assoc .leftInv (inl (inl x)) = refl
⊎-assoc .leftInv (inl (inr x)) = refl
⊎-assoc .leftInv (inr x) = refl

×-assoc : ((A × B) × C) ⇔ (A × (B × C))
×-assoc = Σ-assoc

open import Cubical.Foundations.Everything using (pathToEquiv; equivToIso)

cong-Σ : ∀ {q} {Q : A → Type q} → (∀ x → P x ⇔ Q x) → Σ A P ⇔ Σ A Q
cong-Σ i .fun = map₂ (i _ .fun)
cong-Σ i .inv = map₂ (i _ .inv)
cong-Σ i .rightInv x = ΣPathP (refl , i _ .rightInv _)
cong-Σ i .leftInv  x = ΣPathP (refl , i _ .leftInv _)

cong-⇔ : (f : Type a → Type b) → A ⇔ B → f A ⇔ f B
cong-⇔ f = equivToIso ∘ pathToEquiv ∘ cong f ∘ isoToPath

⇔⇒↠! : A ⇔ B → A ↠! B
⇔⇒↠! f .fst = f .fun
⇔⇒↠! f .snd y .fst = f .inv y
⇔⇒↠! f .snd y .snd = f .rightInv y
