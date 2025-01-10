{-# OPTIONS --safe #-}

module Data.Sigma.Properties where

open import Cubical.Data.Sigma.Properties
  using (Σ≡Prop; discreteΣ; PathPΣ; ΣPathP)
  renaming (Σ-swap-Iso to ⇔-Σ-swap; Σ-assoc-Iso to ⇔-Σ-assoc)
  public

open import Function
open import Level
open import Data.Sigma
open import Isomorphism
open import Path
open import Cubical.Foundations.Everything using (substRefl; subst-filler)
open import HLevels

Π⟨Σ⟩ : (A : Type a) → (P : A → Type p) → Type (a ℓ⊔ p)
Π⟨Σ⟩ A P = Σ[ f ⦂ (A → Σ A P) ] × ∀ x → f x .fst ≡ x

module _ {P : A → Type p} (set : isSet A) where
  Π⇔Σ :
    ((x : A) → P x) ⇔ Π⟨Σ⟩ A P
  Π⇔Σ .fun f .fst x .fst = x
  Π⇔Σ .fun f .fst x .snd = f x
  Π⇔Σ .fun f .snd _ = refl
  Π⇔Σ .inv (f , p) x = subst P (p x) (f x .snd)
  Π⇔Σ .leftInv  f = funExt λ x → substRefl {B = P} (f x)
  Π⇔Σ .rightInv (f , p) =
    Σ≡Prop
      (λ _ → isPropΠ λ _ → set _ _) 
      (sym (funExt λ x → cong₂ _,_ (p x) (subst-filler P (p x) (f x .snd))))

∃!Prop : isSet A → ((x : A) → isProp (P x)) → isProp (∃! P) 
∃!Prop set prop (x , Px , !x) (y , Py , !y) =
  Σ≡Prop (λ x′ → isProp× (prop x′) (isPropΠ λ y′ → isProp→ (set x′ y′))) (!x y Py)
