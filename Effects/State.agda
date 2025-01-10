{-# OPTIONS --safe --lossy-unification #-}

open import Prelude renaming (tt to ⟨⟩)
open import Signatures
open import FinitenessConditions
open import FreeMonad.PackagedTheory

module Effects.State
  (S : Type)
  (finiteState : SplitQuotientedChoiceω S)
  (setState : isSet S)
  where

module StateFunctor where
  data Op : Type where
    `get  : Op
    `put  : S → Op

  Arity : Op → Type
  Arity `get      = S
  Arity (`put _)  = ⊤

open StateFunctor using (`get; `put) public

open StateFunctor

𝕊 : Signature
𝕊 = Op ◁ Arity

Sₘ : Type a → Type a
Sₘ A = S → A × S

open import FreeMonad.Theory hiding (Law; Theory)
import FreeMonad.Theory

Law : Signature → Type₁
Law 𝔽 = FreeMonad.Theory.Law 0 𝔽

Theory : Signature → Type₁
Theory 𝔽 = FreeMonad.Theory.Theory 0 𝔽

module Synt where
  open import FreeMonad.Syntax 𝕊 public hiding (Syntax)
  open import FreeMonad.Syntax public using (Syntax)
  open SyntaxBind public

  put : S → Syntax 𝕊 ⊤
  put s = Op⟦ `put s ⟧

  get : Syntax 𝕊 S
  get = Op⟦ `get ⟧

  toState : (S → A × S) → Syntax 𝕊 A
  toState f =
    do s ← get
       let y , s′ = f s
       put s′
       return y

  open FreeMonad.Theory.Law public
  open Equation public

  module PutPutLawDisplay where
    put-put-law : Law 𝕊
    put-put-law .Γ = S × S
    put-put-law .ν _ = ⊤
    put-put-law .eqn (s₁ , s₂) =
      (do put s₁ ; put s₂) ≐ (do put s₂)
  data Laws : Type 
  data Laws where put-put put-get get-put : Laws
  Eqns : Laws → Law 𝕊
  Eqns put-get .Γ  = S
  Eqns put-get .ν _ = S
  Eqns put-put .Γ = S × S
  Eqns put-put .ν _ = ⊤
  Eqns get-put .Γ  = ⊤
  Eqns get-put .ν _ = ⊤
  Eqns put-put  .eqn (s₁ , s₂)  = (do put s₁; put s₂)  ≐ (do put s₂)
  Eqns put-get  .eqn s          = (do put s; get)      ≐ (do put s; return s)
  Eqns get-put  .eqn _          = (do s ← get; put s)  ≐ (do return ⟨⟩)
  state-alg : 𝕊 -Alg[ (S → A × S) ]
  state-alg (`get     , k) s₁ = k  s₁  s₁
  state-alg (`put s₂  , k) s₁ = k  ⟨⟩  s₂
  runState : Syntax 𝕊 A → S → A × S
  runState = interp state-alg _,_

open Synt using (module PutPutLawDisplay; state-alg) public

StateTheory : Theory 𝕊
StateTheory = record { Synt }


module _ where
  open SplitQuotientedChoiceAt

  finiteOps : ∀ Oᵢ → SplitQuotientedChoiceω (Arity Oᵢ)
  finiteOps `get = finiteState
  finiteOps (`put x) = quotientedChoice⊤

  finiteVars : FiniteVars StateTheory
  finiteVars Synt.put-put _ = quotientedChoice⊤
  finiteVars Synt.get-put _ = quotientedChoice⊤
  finiteVars Synt.put-get _ = finiteState
  
𝕊-theory = full-theory 𝕊 StateTheory finiteOps finiteVars

open import FreeMonad.Quotiented 𝕊-theory renaming (Term to StateTerm) public

open Synt using (op; var)
Term = StateTerm

State : Type a → Type _
State = StateTerm

get : Term S
get = [ op (`get , var) ]

put : S → Term ⊤
put s = [ op (`put s , var) ]

put-put′ : ∀ s₁ s₂ → (do put s₁; put s₂) ≡ (do put s₂)
put-put′ s₁ s₂ = eq/ _ _ (lawₜ Synt.put-put (s₁ , s₂))

modify : (S → S) → Term ⊤
modify f = do s ← get; put (f s)

put-put : ∀ s₁ s₂ (k : Term A) → (do put s₁; put s₂; k) ≡ (do put s₂; k)
put-put s₁ s₂ k = cong (λ p → do p ; k) (put-put′ s₁ s₂)

get-put :
  ∀ (k : State A)
  → (do s ← get
        put s
        k) ≡ k
get-put k = cong (_>> k) (eq/ _ _ (lawₜ Synt.get-put _))

put-get : ∀ s (k : S → State A) → (do put s; s′ ← get; k s′) ≡ (do put s; k s)
put-get s k = cong (λ p → do r ← p; k r) (eq/ _ _ (lawₜ Synt.put-get s))

get-put-get : (k : S → State A) → (do s ← get; put s; k s) ≡ (do s ← get; k s)
get-put-get k =   (do s ← get
                      put s
                      k s)

                                      ≡⟨⟩
                 
                  (do s ← get
                      put s
                      s′ ← return s
                      k s′)

                                      ≡˘⟨ s ⇐ get ⨾/ put-get s k ⟩
                 
                  (do s ← get
                      put s
                      s′ ← get
                      k s′)

                                      ≡⟨ get-put (get >>= k) ⟩
                 
                  (do s ← get
                      k s) ∎

get-get : ∀  (k : S → S → State B) →
             (do s₁ ← get
                 s₂ ← get
                 k s₁ s₂)  ≡ (do s ← get
                                 k s s)

get-get k =

  (do s₁ ← get
      s₂ ← get
      k s₁ s₂)          ≡˘⟨ get-put _ ⟩

  (do s ← get
      put s
      s₁ ← get
      s₂ ← get
      k s₁ s₂)          ≡⟨ s ⇐ get ⨾/ put-get s _ ⟩

  (do s₁ ← get
      put s₁
      s₂ ← get
      k s₁ s₂)          ≡⟨ s₁ ⇐ get ⨾/ put-get s₁ _ ⟩

  (do s ← get
      put s
      k s s)            ≡⟨ get-put-get _ ⟩

  (do s ← get
      k s s) ∎

get-nop : (k : State A) → (get >> k) ≡ k
get-nop k =

  (do get
      k)                  ≡˘⟨ get-put-get (λ _ → k) ⟩

  (do s ← get
      put s
      k)                  ≡⟨ get-put k ⟩

  k ∎

toState : (S → A × S) → Term A
toState k = do s₁ ← get
               let x , s₂ = k s₁
               put s₂
               return x
open import Data.Vec

toState-synt : (f : S → A × S) → toState f ≡ [ Synt.toState f ]
toState-synt f =
  sym (syntactic-bind _ Synt.get ⨾ cong (get >>=_) (funExt (λ s → syntactic-bind (λ _ → Synt.return (f s .fst)) (Synt.put (f s .snd)))))

module _ (truncCarrier : isSet A) where
  module _ where
    open Synt using (put-put; put-get; get-put)

    runState-resp : (state-alg {A = A}) Models StateTheory
    runState-resp put-put t k = refl
    runState-resp put-get t k = refl
    runState-resp get-put t k = refl
  runState : Term A → (S → A × S)
  runState = interpₜ  state-alg
                      (λ x s → x , s)
                      runState-resp
                      ⋯
    where ⋯ = isSetΠ λ _ → isSet× truncCarrier setState

  rinv : ∀ p → runState (toState p) ≡ p
  linv : ∀ p → toState (runState p) ≡ p

  rinv f = cong runState (toState-synt f)

  linv =
    elimProp/
      (λ _ → squash/ _ _)
      (Synt.elim-s (λ xs → toState (Synt.runState xs) ≡ [ xs ]) alg)
    where
    open Synt renaming (var to var) using (DepAlg; op)

    alg : Ψ[ xs ⦂ Syntax A ] (toState (Synt.runState xs) ≡ [ xs ])

    alg (var x) = get-put (return x)

    alg (op (`get , xs) r) =

      (do s ← get
          let y , s′ = Synt.runState (op (`get , xs)) s
          put s′
          return y)                                         ≡⟨⟩

      (do s ← get
          let y , s′ = Synt.runState (xs s) s
          put s′
          return y)                                         ≡˘⟨ get-get _ ⟩

      (do s₁ ← get
          s₂ ← get
          let y , s₃ = Synt.runState (xs s₁) s₂
          put s₃
          return y)                                         ≡⟨ s ⇐ get ⨾/ r s ⟩

      (do s ← get
          [ xs s ])                                         ≡˘⟨ syntactic-bind xs Synt.get ⟩

      [ op (`get , xs) ] ∎

    alg (op (`put x , xs) r) =

      toState (Synt.runState (op (`put x , xs)))                      ≡⟨⟩

      (do s₁ ← get
          let y , s₂ = Synt.runState (op (`put x , xs)) s₁
          put s₂
          return y)                                                   ≡⟨⟩

      (do s₁ ← get
          let y , s₂ = Synt.runState (xs ⟨⟩) x
          put s₂
          return y)                                                   ≡⟨ get-nop _ ⟩

      (do let y , s₂ = Synt.runState (xs ⟨⟩) x
          put s₂
          return y)                                                   ≡˘⟨ put-put _ _ (return (fst (Synt.runState (xs ⟨⟩) x))) ⟩

      (do put x
          let y , s₂ = Synt.runState (xs ⟨⟩) x
          put s₂
          return y)                                                   ≡˘⟨ put-get _ _ ⟩

      (do put x
          s₁ ← get
          let y , s₂ = Synt.runState (xs ⟨⟩) s₁
          put s₂
          return y)                                                   ≡⟨ cong (put x >>_) (r ⟨⟩) ⟩

      (do put x
          [ xs ⟨⟩ ])                                                   ≡⟨⟩

      [ op (`put x , xs) ] ∎
      
  state-iso : State A ⇔ (S → A × S)
  state-iso .fun = runState
  state-iso .inv = toState
  state-iso .rightInv = rinv
  state-iso .leftInv = linv

open import Truth hiding (Ω)
open import Truth.Definition 0
open import Truth.Definition 1 using () renaming (Ω to Ω₁) 

