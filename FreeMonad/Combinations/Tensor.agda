{-# OPTIONS --safe #-}

open import Prelude
open import FreeMonad.PackagedTheory
open import Signatures
open import FinitenessConditions

module FreeMonad.Combinations.Tensor
  {ℓ}
  (T₁ : FullTheory ℓ)
  (T₂ : FullTheory ℓ)
  where

import FreeMonad.Combinations.Sum T₁ T₂ as SumTheory

open import FreeMonad.Combinations.Sum T₁ T₂
  hiding (𝒯; finVars; lift₁; lift₂; combinedTheory)
  public

open FullTheory T₁ renaming (𝒯 to 𝒯₁; finiteArity to finAr₁; finiteVars to finVar₁)
open FullTheory T₂ renaming (𝔽 to 𝔾; 𝒯 to 𝒯₂; finiteArity to finAr₂; finiteVars to finVar₂)

open Signature

open import FreeMonad.Theory
open import FreeMonad.Syntax hiding (Op⟦_⟧)
open import FreeMonad.Syntax (𝔽 ⊞ 𝔾) using (Op⟦_⟧)

module _ where
  open SyntaxBind (𝔽 ⊞ 𝔾)
  commutative : Law ℓ (𝔽 ⊞ 𝔾)
  commutative .Γ = Lift (Op 𝔽 × Op 𝔾)
  commutative .ν (lift (fs , gs)) = Lift (Arity 𝔽 fs × Arity 𝔾 gs)
  commutative .eqn = λ {
    (lift (fs , gs)) →  (do f  ← Op⟦ inl fs  ⟧ ; g  ← Op⟦ inr gs  ⟧ ; return (lift (f , g)))
                                              ≐
                        (do g  ← Op⟦ inr gs  ⟧ ; f  ← Op⟦ inl fs  ⟧ ; return (lift (f , g)))
    }

open Theory

𝒯′ : Theory _ _
𝒯′ .Laws = ⊤
𝒯′ .Eqns _ = commutative

finVars′ : FiniteVars 𝒯′
finVars′ _ (lift (γ₁ , γ₂)) = quotientedChoiceLift (quotientedChoiceProd (finAr₁ γ₁) (finAr₂ γ₂))

open import FreeMonad.Combinations.Quotient SumTheory.combinedTheory 𝒯′ finVars′ public

open import FreeMonad.Quotiented combinedTheory
import FreeMonad.Quotiented SumTheory.combinedTheory as SumQuot

lift₁ : F₁.Term A → Term A
lift₁ = F₁.interpₜ (opₜ ∘ inl-map) return resp squash/
  where
  resp : (opₜ ∘ inl-map) Models 𝒯₁
  resp i t k = 
    let lhs ≐ rhs = Theory.Eqns 𝒯₁ i .eqn t
    in interp _ (opₜ ∘ inl-map) k lhs ≡⟨ inj₁-com opₜ k lhs ⟩
       interp _ opₜ k (inj₁ lhs) ≡⟨ opₜ-resp (inl (inl i)) t k  ⟩
       interp _ opₜ k (inj₁ rhs) ≡˘⟨ inj₁-com opₜ k rhs ⟩
       interp _ (opₜ ∘ inl-map) k rhs ∎

lift₂ : F₂.Term A → Term A
lift₂ = F₂.interpₜ (opₜ ∘ inr-map) return resp squash/
  where
  resp : (opₜ ∘ inr-map) Models 𝒯₂
  resp i t k = 
    let lhs ≐ rhs = Theory.Eqns 𝒯₂ i .eqn t
    in interp _ (opₜ ∘ inr-map) k lhs ≡⟨ inj₂-com opₜ k lhs ⟩
       interp _ opₜ k (inj₂ lhs) ≡⟨ opₜ-resp (inl (inr i)) t k  ⟩
       interp _ opₜ k (inj₂ rhs) ≡˘⟨ inj₂-com opₜ k rhs ⟩
       interp _ (opₜ ∘ inr-map) k rhs ∎

lift₂-com : (O : Op 𝔾) (k : Arity 𝔾 O → F₂.Term B)
          → lift₂ (F₂.opₜ (O , k)) ≡ opₜ (inr O , lift₂ ∘ k)
lift₂-com O = F₂.elim~canonical _ (λ _ → squash/ _ _) λ k → cong lift₂ (F₂.opₜ-com-[] k) 

lift₁-com : (O : Op 𝔽) (k : Arity 𝔽 O → F₁.Term B)
          → lift₁ (F₁.opₜ (O , k)) ≡ opₜ (inl O , lift₁ ∘ k)
lift₁-com O = F₁.elim~canonical _ (λ _ → squash/ _ _) λ k → cong lift₁ (F₁.opₜ-com-[] k) 

commutes′ : (f : Op 𝔽) (g : Op 𝔾) (k : Arity 𝔽 f → Arity 𝔾 g → Syntax (𝔽 ⊞ 𝔾) A)
         → op (inl f , λ x → op (inr g , λ y → k x y)) ~ₜ op (inr g , λ y → op (inl f , λ x → k x y))
commutes′ f g k = >>=-cong (uncurry k ∘ lower) (eqₜ (inr tt) (lift (f , g)) Syntax.var)

commutes : (f : Op 𝔽) (g : Op 𝔾) (k : Arity 𝔽 f → Arity 𝔾 g → Term A)
         → (do x ← Opₜ⟦ inl f ⟧ ; y ← Opₜ⟦ inr g ⟧ ; k x y) ≡ (do y ← Opₜ⟦ inr g ⟧ ; x ← Opₜ⟦ inl f ⟧ ; k x y)
commutes f g k = cong (_>>= (uncurry k ∘ lower)) (eq/ _ _ (eqₜ (inr tt) (lift (f , g)) Syntax.var))

commutes-mult₁ : (fs : Op 𝔽) (ys : F₂.Term B) (k : Arity 𝔽 fs → B → Term C)
               → (do f ← [ op (inl fs , Syntax.var) ] ; y ← lift₂ ys ; k f y) ≡ (do y ← lift₂ ys ; f ← [ op (inl fs , Syntax.var) ] ; k f y)
commutes-mult₁ fs ys k =
  elimProp/
    {P = λ ys → (do f ← [ op (inl fs , Syntax.var) ] ; y ← lift₂ ys ; k f y) ≡ (do y ← lift₂ ys ; f ← [ op (inl fs , Syntax.var) ] ; k f y)}
    (λ _ → squash/ _ _)
    (elim-s _ _ (λ { (var x) → refl
                   ; (op (Oy , ys) P⟨ys⟩) →

                     (do f ← [ op (inl fs , Syntax.var) ] ; y ← lift₂ [ op (Oy , ys) ] ; k f y) ≡⟨ f ⇐ [ op (inl fs , Syntax.var) ] ⨾/ assoc [ op (inr Oy , Syntax.var) ] _ _ ⟩
                     (do f ← [ op (inl fs , Syntax.var) ] ; y′ ← [ op (inr Oy , Syntax.var) ] ; y ← lift₂ [ ys y′ ] ; k f y) ≡⟨ commutes fs Oy _ ⟩
                     (do y′ ← [ op (inr Oy , Syntax.var) ] ; f ← [ op (inl fs , Syntax.var) ] ; y ← lift₂ [ ys y′ ] ; k f y) ≡⟨ y′ ⇐ [ op (inr Oy , Syntax.var) ] ⨾/ P⟨ys⟩ y′ ⟩
                     (do y′ ← [ op (inr Oy , Syntax.var) ] ; y ← lift₂ [ ys y′ ] ; f ← [ op (inl fs , Syntax.var) ] ; k f y) ≡˘⟨ assoc [ op (inr Oy , Syntax.var) ] _ _ ⟩
                     (do y ← ([ op (inr Oy , Syntax.var) ] >>= λ y′ → lift₂ [ ys y′ ]) ; f ← [ op (inl fs , Syntax.var) ] ; k f y) ≡⟨⟩
                     (do y ← opₜ (inr Oy , λ y′ → lift₂ [ ys y′ ]) ; f ← [ op (inl fs , Syntax.var) ] ; k f y) ≡⟨⟩
                     (do y ← lift₂ [ op (Oy , ys) ] ; f ← [ op (inl fs , Syntax.var) ] ; k f y) ∎

                   }))
    ys

commutes-mult : (xs : F₁.Term A) (ys : F₂.Term B) (k : A → B → Term C)
              → (do x ← lift₁ xs ; y ← lift₂ ys ; k x y) ≡ (do y ← lift₂ ys ; x ← lift₁ xs ; k x y)
commutes-mult xs ys k =
  elimProp/
    {P = λ xs → (do x ← lift₁ xs ; y ← lift₂ ys ; k x y) ≡ (do y ← lift₂ ys ; x ← lift₁ xs ; k x y)}
    (λ _ → squash/ _ _)
    (elim-s _ _ λ { (var x) → refl ; (op (Ox , xs) P⟨xs⟩) →

    (do x ← lift₁ [ op (Ox , xs) ]
        y ← lift₂ ys
        k x y) ≡⟨ assoc [ op (inl Ox , Syntax.var) ] _ _ ⟩

    (do i ← [ op (inl Ox , Syntax.var) ]
        x ← lift₁ [ xs i ]
        y ← lift₂ ys
        k x y) ≡⟨ i ⇐ [ op (inl Ox , Syntax.var) ] ⨾/ P⟨xs⟩ i ⟩

    (do i ← [ op (inl Ox , Syntax.var) ]
        y ← lift₂ ys
        x ← lift₁ [ xs i ]
        k x y) ≡⟨ commutes-mult₁ Ox ys _ ⟩

    (do y ← lift₂ ys
        i ← [ op (inl Ox , Syntax.var) ]
        x ← lift₁ [ xs i ]
        k x y) ≡˘⟨ y ⇐ lift₂ ys ⨾/ assoc [ op (inl Ox , Syntax.var) ] _ _ ⟩

    (do y ← lift₂ ys
        x ← lift₁ [ op (Ox , xs) ]
        k x y) ∎

    })
    xs

⊗-resp : (ϕ : 𝔽 -Alg[ A ]) (ψ : 𝔾 -Alg[ A ])
       → (∀ t → (ϕ -⊞- ψ) Respects (commutative .eqn t))
       → ϕ Models 𝒯₁
       → ψ Models 𝒯₂
       → (ϕ -⊞- ψ) Models 𝒯
⊗-resp ϕ ψ resp⊞ resp₁ resp₂ (inr tt) t k = resp⊞ t k
⊗-resp ϕ ψ resp⊞ resp₁ resp₂ (inl (inl i)) t k = let lhs ≐ rhs = Theory.Eqns 𝒯₁ i .eqn t in interp₁ ϕ ψ k lhs ⨾ resp₁ i t k ⨾ sym (interp₁ ϕ ψ k rhs)
⊗-resp ϕ ψ resp⊞ resp₁ resp₂ (inl (inr i)) t k = let lhs ≐ rhs = Theory.Eqns 𝒯₂ i .eqn t in interp₂ ϕ ψ k lhs ⨾ resp₂ i t k ⨾ sym (interp₂ ϕ ψ k rhs)
