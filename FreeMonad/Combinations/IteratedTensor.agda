{-# OPTIONS --safe #-}

open import Prelude
open import FreeMonad.PackagedTheory
open import Signatures
open import FinitenessConditions

module FreeMonad.Combinations.IteratedTensor
  {ℓ}
  (I : Type)
  (Tₙ : I → FullTheory ℓ)
  where

open Signature
open import FreeMonad.Syntax hiding (Op⟦_⟧)

module _ (i : I) where
  open FullTheory (Tₙ i) public renaming (𝒯 to 𝒯ₙ)
open FreeMonad.Syntax (Σ◁ I 𝔽) using (Op⟦_⟧)
open SyntaxBind (Σ◁ I 𝔽)
open import FreeMonad.Theory ℓ (Σ⟦ i ⦂ I ⟧ ◁ 𝔽 i)

commutative : I → I → Law 
commutative i j .Γ = Lift (i ≢ j × 𝔽 i .Op × 𝔽 j .Op)
commutative i j .ν (lift (_ , fs , gs)) = Lift (Arity (𝔽 i) fs × Arity (𝔽 j) gs)
commutative i j .eqn (lift (_ , fs , gs)) =
                   (do f  ← Op⟦ i  , fs  ⟧ ; g  ← Op⟦ j  , gs  ⟧ ; return (lift (f , g)))
                                                      ≐
                   (do g  ← Op⟦ j  , gs  ⟧ ; f  ← Op⟦ i  , fs  ⟧ ; return (lift (f , g)))

𝒯′ : Theory
𝒯′ .Theory.Laws = I × I
𝒯′ .Theory.Eqns = uncurry commutative

finVars′ : FiniteVars 𝒯′
finVars′ (i , j) (lift (_ , lhs , rhs)) =
  quotientedChoiceLift (quotientedChoiceProd (finiteArity i lhs) (finiteArity j rhs))

open import FreeMonad.Combinations.Sigma I Tₙ renaming (combinedTheory to sigmaTheory)
open import FreeMonad.Combinations.Sigma I Tₙ using (inj) public
open import FreeMonad.Combinations.Quotient sigmaTheory 𝒯′ finVars′ public
