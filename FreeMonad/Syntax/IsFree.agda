open import Prelude
open import Signatures

module FreeMonad.Syntax.IsFree (𝔽 : Signature) where

open import FreeMonad.Syntax 𝔽

private variable ν : Type

η : A → Syntax A
η = var

module _ {A C : Type} (ϕ : 𝔽 -Alg[ C ]) (f : A → C) where
  h : (Syntax A , op) ⟶ (C , ϕ)
  h .fst = interp ϕ f
  h .snd = refl

  cancel : h .fst ∘ η ≡ f
  cancel = refl

  module _ (g : (Syntax A , op) ⟶ (C , ϕ)) (g-cancel : g .fst ∘ η ≡ f) where
    uniq : ∀ x → h .fst x ≡ g .fst x
    uniq (var x) = cong (_$ x) (sym g-cancel)
    uniq (op (O , x)) = cong (ϕ ∘ _,_ O) (funExt λ i → uniq (x i)) ⨾ sym (cong (_$ (O , x)) (g .snd))
