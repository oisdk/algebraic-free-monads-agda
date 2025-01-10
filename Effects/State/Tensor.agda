{-# OPTIONS --lossy-unification --safe #-}

open import Prelude
open import FreeMonad.PackagedTheory
open import FinitenessConditions
open import Signatures
open import FreeMonad.Syntax
open import FreeMonad.Theory

module Effects.State.Tensor
  (S : Type)
  (choiceState : SplitQuotientedChoiceω S)
  (setState : isSet S)
  (ℱ-theory : FullTheory 0)
  where

import Effects.State S choiceState setState as 𝒮
open import FreeMonad.Combinations.Tensor ℱ-theory 𝒮.𝕊-theory

open FullTheory ℱ-theory using (𝔽) renaming (𝒯 to 𝒯𝒻)

open 𝒮 using (𝕊) renaming (StateTheory to 𝒯𝓈)

State-Synt : Type a → Type _
State-Synt A = S → Syntax 𝔽 (A × S)

import FreeMonad.Quotiented ℱ-theory as ℱ
import FreeMonad.Quotiented 𝒮.𝕊-theory as 𝒮t

State-Term : Type a → Type _
State-Term A = S → ℱ.Term (A × S)

module _ {A : Type a} where
  runState-alg : 𝕊 -Alg[ State-Term A ]
  runState-alg (𝒮.`get   , k) s = k s  s
  runState-alg (𝒮.`put s , k) _ = k tt s

  inj-alg : 𝔽 -Alg[ State-Term A ]
  inj-alg xs s = ℱ.opₜ (cmap (λ r → r s) xs)

  inj-alg-resp : inj-alg Models 𝒯𝒻
  inj-alg-resp i t k = funExt λ s →
    let lhs ≐ rhs = 𝒯𝒻 .Theory.Eqns i .eqn t
    in  interp 𝔽 inj-alg k lhs s       ≡⟨ interp-fusion 𝔽 (_$ s) _ (λ _ → refl) lhs ⟩
        interp 𝔽 ℱ.opₜ (flip k s) lhs  ≡⟨ ℱ.opₜ-resp i t (flip k s) ⟩
        interp 𝔽 ℱ.opₜ (flip k s) rhs  ≡˘⟨ interp-fusion 𝔽 (_$ s) _ (λ _ → refl) rhs ⟩
        interp 𝔽 inj-alg k rhs s ∎

  runState-resp : (runState-alg ⦂ 𝕊 -Alg[ State-Term A ]) Models 𝒯𝓈
  runState-resp 𝒮.Synt.Laws.put-put t k = refl
  runState-resp 𝒮.Synt.Laws.put-get t k = refl
  runState-resp 𝒮.Synt.Laws.get-put t k = refl

  runStateT-alg : (𝔽 ⊞ 𝕊) -Alg[ State-Term A ]
  runStateT-alg = inj-alg -⊞- runState-alg

  runStateT-ret : A → State-Term A
  runStateT-ret x s = ℱ.return (x , s)

  runStateT-commutes : ∀ t → runStateT-alg Respects commutative .eqn t
  runStateT-commutes (lift (xs , 𝒮.`get   )) k = refl
  runStateT-commutes (lift (xs , 𝒮.`put s )) k = refl

  runStateT-resp : runStateT-alg Models 𝒯
  runStateT-resp = ⊗-resp inj-alg runState-alg  runStateT-commutes inj-alg-resp runState-resp 

module Synt where
  open SyntaxBind (𝔽 ⊞ 𝕊) public

  put : S → Syntax (𝔽 ⊞ 𝕊) ⊤
  put x = op (inr (𝒮.`put x) , var)

  get : Syntax (𝔽 ⊞ 𝕊) S
  get = op (inr 𝒮.`get , var)

  runStateT : Syntax (𝔽 ⊞ 𝕊) A → State-Term A
  runStateT = interp _ runStateT-alg runStateT-ret

open import FreeMonad.Quotiented combinedTheory renaming (Term to State)

put : S → State ⊤
put x = [ Synt.put x ]

get : State S
get = [ Synt.get ]

put-put : ∀ s₁ s₂ (k : State A) → put s₁ >> (put s₂ >> k) ≡ put s₂ >> k
put-put s₁ s₂ k = cong (_>> k) (eq/ _ _ (lawₜ (inl (inr 𝒮.Synt.put-put)) (s₁ , s₂)))

get-put : ∀ (k : State A) → (do s ← get ; put s ; k) ≡ k
get-put k = cong (_>> k) (eq/ _ _ (lawₜ (inl (inr 𝒮.Synt.get-put)) _))

put-get : ∀ s (k : S → State A) → (do put s ; s′ ← get ; k s′) ≡ (do put s ; k s)
put-get s k = cong (_>>= k) (eq/ _ _ (lawₜ (inl (inr 𝒮.Synt.put-get)) s))

get-put-get : (k : S → State A) →
              (do s ← get ; put s ; k s)  ≡ (do s ← get ; k s)
get-put-get k =

  (do s ← get
      put s
      k s)                                 ≡⟨⟩

  (do s ← get
      put s
      s′ ← return s
      k s′)                                ≡˘⟨ s ⇐ get ⨾/ put-get s k ⟩

  (do s ← get
      put s
      s′ ← get
      k s′)                                ≡⟨ get-put (get >>= k) ⟩

  (do s ← get
      k s) ∎

get-get : ∀ (k : S → S → State B) →
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

liftT : ℱ.Term A → State A
liftT = lift₁

liftT-lemma : (xs : Syntax 𝔽 A) → [ inj₁ xs ] ≡ liftT [ xs ]
liftT-lemma = elim-s _ _ λ { (var x) → refl ; (op (O , xs) P⟨xs⟩) → sym (opₜ-com-[] _) ⨾ cong (opₜ ∘ _,_ (inl O)) (funExt P⟨xs⟩) }

state-commutes : ∀ Sₒ O → (k : Signature.Arity 𝕊 Sₒ → Signature.Arity 𝔽 O → State A) → opₜ (inr Sₒ , λ s → opₜ (inl O , k s)) ≡ opₜ (inl O , λ i → opₜ (inr Sₒ , flip k i))
state-commutes Sₒ o k = sym (commutes o Sₒ (flip k))

state-commutes-mult : (xs : 𝒮t.Term A) (ys : ℱ.Term B) (k : A → B → State C)
                    → (do x ← lift₂ xs ; y ← lift₁ ys ; k x y) ≡ (do y ← lift₁ ys ; x ← lift₂ xs ; k x y)
state-commutes-mult xs ys k = sym (commutes-mult ys xs (flip k))

pattern `put s = inr (𝒮.`put s)
pattern `get   = inr  𝒮.`get

module _ {A : Type a} where
  toStateT : State-Term A → State A
  toStateT f =
    do s ← get
       y , s′ ← liftT (f s)
       put s′
       return y

  runStateT : State A → State-Term A
  runStateT = interpₜ runStateT-alg runStateT-ret runStateT-resp (isSetΠ λ _ →  squash/)

  stateT-iso : State A ⇔ State-Term A
  stateT-iso .fun = runStateT
  stateT-iso .inv = toStateT

  stateT-iso .rightInv =
    SplitQuotientedChoiceAt.elim~canonical
      choiceState _ (λ _ → isSetΠ (λ _ → squash/) _ _)
      λ k → funExt λ s₁ →

      runStateT (do s₂ ← get
                    y , s₃ ← liftT [ k s₂ ]
                    put s₃
                    return y) s₁                                                ≡˘⟨ cong (flip runStateT s₁) (s₂ ⇐ get ⨾/ cong (_>>= _) (liftT-lemma (k s₂))) ⟩

      runStateT (do s₂ ← get
                    y , s₃ ← [ inj₁ (k s₂) ]
                    put s₃
                    return y) s₁                                                ≡˘⟨ cong (flip runStateT s₁) (syntactic-bind _ Synt.get ⨾ s₂ ⇐ get ⨾/ syntactic-bind _ (inj₁ (k s₂)) ) ⟩


      runStateT [ Synt.get Synt.>>= (λ s₂ →
                  inj₁ (k s₂) Synt.>>= λ { (y , s₃) →
                  Synt.put s₃ Synt.>>
                  Synt.return y
                }) ] s₁                                                         ≡⟨⟩

      Synt.runStateT (inj₁ (k s₁) Synt.>>= (λ { (y , s₃) →
                      Synt.put s₃ Synt.>>
                      Synt.return y })) s₁                                      ≡⟨⟩

      Synt.runStateT
        (interp _ op (λ { (y , s₃) → Synt.put s₃ Synt.>> Synt.return y })
          (inj₁ (k s₁))) s₁                                                     ≡⟨ cong (_$ s₁) (interp-comp _ runStateT-alg runStateT-ret _ (inj₁ (k s₁))) ⟩

      interp _ runStateT-alg
        (Synt.runStateT ∘ (λ { (y , s₃) → Synt.put s₃ Synt.>> Synt.return y }))
        (inj₁ (k s₁)) s₁                                                        ≡⟨⟩

      interp _ runStateT-alg (const ∘ ℱ.return) (inj₁ (k s₁)) s₁                ≡⟨ cong (_$ s₁) (interp₁ inj-alg runState-alg _ (k s₁)) ⟩

      interp _ inj-alg (const ∘ ℱ.return) (k s₁) s₁                             ≡˘⟨ cong (_$ s₁) (interp-fusion _ (const ∘ [_]) Syntax.var (λ xs → funExt λ s → sym (ℱ.opₜ-com-[] _)) (k s₁)) ⟩

      [ interp _ op Syntax.var (k s₁) ]                                         ≡⟨ cong [_] (interp-id _ (k s₁)) ⟩

      [ k s₁ ] ∎

  stateT-iso .leftInv = elimProp/ (λ _ → squash/ _ _) (elim-s _ _ leftInv-alg)
    where
    leftInv-alg : DepAlg (𝔽 ⊞ 𝕊) A λ xs → toStateT (runStateT [ xs ]) ≡ [ xs ]

    leftInv-alg (var x) =

      toStateT (runStateT (return x))              ≡⟨⟩

      toStateT (λ s → [ Syntax.var (x , s) ])      ≡⟨⟩

      (do s ← get
          y , s′ ← liftT [ Syntax.var (x , s) ]
          put s′
          return y)                                ≡⟨⟩

      (do s ← get
          put s
          return x)                                ≡⟨ get-put _ ⟩

      return x ∎

    leftInv-alg (op (`get , k) P⟨xs⟩) =

      toStateT (runStateT [ Syntax.op (`get , k) ])                   ≡⟨⟩

      (do s ← get
          y , s′ ← liftT (runStateT [ Syntax.op (`get , k) ] s)
          put s′
          return y)                                                   ≡⟨⟩

      (do s ← get
          y , s′ ← liftT (runStateT [ k s ] s)
          put s′
          return y)                                                   ≡˘⟨ get-get _ ⟩

      (do s₁ ← get
          s₂ ← get
          y , s′ ← liftT (runStateT [ k s₁ ] s₂)
          put s′
          return y)                                                   ≡⟨ s₁ ⇐ get ⨾/ P⟨xs⟩ s₁ ⟩

      (do s₁ ← get
          [ k s₁ ])                                                   ≡˘⟨ syntactic-bind k Synt.get ⟩

      [ Syntax.op (`get , k) ] ∎


    leftInv-alg (op (`put x , k) P⟨xs⟩) =

      toStateT (runStateT [ op (`put x , k) ])                        ≡⟨⟩

      (do s₁ ← get
          y , s₂ ← liftT (runStateT [ op (`put x , k) ] s₁)
          put s₂
          return y)                                                   ≡⟨⟩

      (do s₁ ← get
          y , s₂ ← liftT (runStateT [ k tt ] x)
          put s₂
          return y)                                                   ≡⟨ get-nop _ ⟩

      (do y , s₂ ← liftT (runStateT [ k tt ] x)
          put s₂
          return y)                                                   ≡˘⟨ (y , s₂) ⇐ liftT (runStateT [ k tt ] x) ⨾/ put-put _ _ (return y) ⟩

      (do y , s₂ ← liftT (runStateT [ k tt ] x)
          put x
          put s₂
          return y)                                                   ≡˘⟨ state-commutes-mult [ 𝒮.Synt.put x ] (runStateT [ k tt ] x) _ ⟩

      (do put x
          y , s₂ ← liftT (runStateT [ k tt ] x)
          put s₂
          return y)                                                   ≡˘⟨ put-get _ _ ⟩

      (do put x
          s₁ ← get
          y , s₂ ← liftT (runStateT [ k tt ] s₁)
          put s₂
          return y)                                                   ≡⟨ cong (put x >>_) (P⟨xs⟩ tt) ⟩

      (do put x
          [ k tt ])                                                   ≡⟨⟩

      [ op (`put x , k) ] ∎

    leftInv-alg (op (inl O , k) P⟨xs⟩) =

      toStateT (runStateT [ Syntax.op (inl O , k) ])                     ≡⟨⟩

      (do s ← get
          y , s′ ← liftT (ℱ.opₜ (O , λ i → runStateT [ k i ] s))
          put s′
          return y)                                                      ≡⟨ s ⇐ get ⨾/ cong (_>>= λ { (y , s′) → put s′ >> return y }) ((lift₁-com O (flip runStateT s ∘ [_] ∘ k))) ⟩

      (do s ← get
          y , s′ ← opₜ (inl O , λ i → liftT (runStateT [ k i ] s))
          put s′
          return y)                                                      ≡⟨ s ⇐ get ⨾/ algebraic (inl O) (λ { (y , s′) → put s′ >> return y }) (liftT ∘ flip runStateT s ∘ [_] ∘ k) ⟩

      (do s ← get
          opₜ (inl O , λ i → do y , s′ ← liftT (runStateT [ k i ] s)
                                put s′
                                return y))                               ≡⟨ state-commutes 𝒮.`get O (λ s i → liftT (runStateT [ k i ] s) >>= λ ys′ →  put (snd ys′) >> return (fst ys′)) ⟩

      opₜ (inl O , λ i → do s ← get
                            y , s′ ← liftT (runStateT [ k i ] s)
                            put s′
                            return y)                                    ≡⟨ cong (opₜ ∘ _,_ (inl O)) (funExt P⟨xs⟩) ⟩

      opₜ (inl O , λ i → [ k i ])                                        ≡⟨ opₜ-com-[] k ⟩

      [ Syntax.op (inl O , k) ] ∎

