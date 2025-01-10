{-# OPTIONS --lossy-unification --safe #-}

open import Prelude renaming (tt to ⟨⟩)
open import Signatures
open import FinitenessConditions
open import FreeMonad.PackagedTheory
open import Data.String.Properties renaming (discreteChar to _≟_)

module Effects.Parser.HElim
  (choiceString : SplitQuotientedChoiceω String)
  where

open import Effects.Parser choiceString
open import Effects.Parser.TreeParser choiceString

open import Hoare.Definition ℙ-theory
open import Hoare.Calculus ℙ-theory
open import Hoare.Lemmas ℙ-theory

open Signature (FullTheory.𝔽 ℙ-theory)

open import Truth

push-remaining : ∀ s → ⟅⟆ r ← (do r ← get; put (s ++ r); return r) ⟅ remaining (s ++ r) ⟆
push-remaining s =
  (λ r → put-remaining (s ++ r)) ⦂
    (∀ r → ⟅⟆ _ ← put (s ++ r) ⟅ remaining (s ++ r) ⟆ )
      ⇒⟨ seq ⟨return True ⟩ (const ⟨return True ⟩) (λ { (r , _) → ⟨remaining⟩ (s ++ r) }) (⟅→⟆True (return True) get) ⟩
    ⟅⟆ (r , _) ← (get ⨾, (λ r → put (s ++ r))) ⟅ remaining (s ++ r) ⟆
      ⇒⟨ focus fst ⟩
    ⟅⟆ r ← fst <$> (get ⨾, (λ r → put (s ++ r))) ⟅ remaining (s ++ r) ⟆
      ⇒⟨ subst-⟅⟆ (assoc get _ _) ⟩
    ⟅⟆ r ← (do r ← get; put (s ++ r); return r) ⟅ remaining (s ++ r) ⟆

remaining-get : ∀ r → ⟅ remaining r ⟆ r′ ← get ⟅ return (r |≡| r′) ⟆
remaining-get r .proof k =

  (do a ← remaining r
      r′ ← get
      k r′ (a |→| (r |≡| r′))) ≡⟨ assoc get _ _ ⟩

  (do r″ ← get
      r′ ← get
      k r′ ((r |≡| r″) |→| (r |≡| r′))) ≡⟨ get-get _ ⟩

  (do r′ ← get
      k r′ ((r |≡| r′) |→| (r |≡| r′))) ≡⟨ r′ ⇐ get ⨾/ cong (k r′) (|→|-id _) ⟩

  (do r′ ← get
      k r′ True) ≡˘⟨ get-nop (do r′ ← get; k r′ True) ⟩

  (do _ ← get
      r′ ← get
      k r′ True) ≡˘⟨ assoc get _ _ ⟩

  (do a ← remaining r
      r′ ← get
      k r′ True) ∎

parse-put-print : ∀ s (p : Term A) v →
     s ∈ p ↦ v →  ⟅⟆
                     ((r , v′) , r′) ← (do  r ← get
                                            put (s ++ r)
                                            v′ ← p
                                            r′ ← get
                                            return ((r , v′) , r′))
                  ⟅ return ((r |≡| r′) |∧| (v |≡| v′)) ⟆
parse-put-print s p v s∈p↦v =
  s∈p↦v ⦂
    s ∈ p ↦ v
      ⇒⟨⟩
    (∀ r → ⟅ remaining (s ++ r) ⟆ v′ ← p ⟅ return (v |≡| v′) ⟨∧⟩ remaining r ⟆)
      ⇒⟨ seq ⟨return True ⟩
             (λ r → ⟨remaining⟩ (s ++ r))
             (λ { (r , v′) → return (v |≡| v′) ⟨∧⟩ remaining r , sef-<$> _ _ (sef-rem r) , det-<$> _ _ (det-rem r) } )
             {p = (do r ← get; put (s ++ r); return r)}
             {q = const p}
             (push-remaining s) ⟩
    ⟅⟆ (r , v′) ← ((do r ← get; put (s ++ r); return r) ⟪,⟫ p) ⟅ return (v |≡| v′) ⟨∧⟩ remaining r ⟆
      ⇒⟨ subst-⟅⟆ (assoc get _ _) ⟩
    ⟅⟆ (r , v′) ← (do r ← get; put (s ++ r); v′ ← p; return (r , v′)) ⟅ return (v |≡| v′) ⟨∧⟩ remaining r ⟆
      ⇒⟨ ⟅∙⟆≡ (λ { (r , v′) → assoc get _ _ ⨾ (r′ ⇐ get ⨾/ cong return (∧-com (v |≡| v′) (r |≡| r′)) ) ⨾ sym (assoc get _ _) }) ⟩
    ⟅⟆ (r , v′) ← (do r ← get; put (s ++ r); v′ ← p; return (r , v′)) ⟅ remaining r ⟨∧⟩ return (v |≡| v′) ⟆
      ⇒⟨ flip (seq ⟨return True ⟩ (λ { (r , v′) → remaining r ⟨∧⟩ return (v |≡| v′) ,  sef-<$> _ _ (sef-rem r) , det-<$> _ _ (det-rem r) }) λ { ((r , v′) , r′) → ⟨return ((r |≡| r′) |∧| (v |≡| v′)) ⟩ })
           ( λ { (r , v′) → ⟨&&&⟩ʳ (remaining r) (λ r′ → return (r |≡| r′)) (v |≡| v′) get (remaining-get r) }) ⟩
    ⟅⟆ ((r , v′) , r′) ← (do r ← get; put (s ++ r); v′ ← p; return (r , v′)) ⟪,⟫ get ⟅ return ((r |≡| r′) |∧| (v |≡| v′)) ⟆
      ⇒⟨ subst-⟅⟆ (assoc get _ _ ⨾ r ⇐ get ⨾/ assoc (put (s ++ r)) (const (p >>= λ v′ → return (r , v′))) _ ⨾  _ ⇐ put (s ++ r) ⨾/ assoc p (λ v′ → return (r , v′)) _) ⟩
    ⟅⟆ ((r , v′) , r′) ← (do r ← get; put (s ++ r); v′ ← p; r′ ← get; return ((r , v′) , r′)) ⟅ return ((r |≡| r′) |∧| (v |≡| v′)) ⟆


open import Finite

open import Data.String.Properties

open import FreeMonad.Modalities ℙ-theory
open import FreeMonad.Syntax (FullTheory.𝔽 ℙ-theory)
open import Data.Tree

import Effects.NonDet as NDM
open NDM.NonDet using (`<|>; `fail)

import Effects.State as STM
open STM.StateFunctor using (`get; `put)

module _ {A : Type a} where
  Totalₛ : Syntax A → Type
  Totalₛ (op (inl `fail , _)) = ⊥
  Totalₛ _ = ⊤

  Total : Term A → Type a
  Total = □ₚ Totalₛ

  Total-nop : ∀ r t → Total t → (do t; put r) ≡ put r
  Total-nop r t (s , e , p) =
      cong (_>> put r) (sym e)
    ⨾ elim-s (λ s → (p : □ₛₚ Totalₛ s) → [ s ] >> put r ≡ put r)
      (λ { (var x) _ → refl
         ; (op (inl `<|> , k) P⟨xs⟩) (p , ps) → cong₂ _<|>_ (P⟨xs⟩ false (ps false)) (P⟨xs⟩ true (ps true)) ⨾ <|>-idem (put r)
         ; (op (inr (`put s) , k) P⟨xs⟩) (_ , ps) →
           [ op (inr (`put s) , k) ] >> put r ≡⟨ cong (_>> put r) (syntactic-bind k Op⟦ inr (`put s) ⟧) ⟩
           (do put s; [ k ⟨⟩ ]) >> put r ≡⟨ assoc (put s) (λ _ → [ k ⟨⟩  ]) (λ _ → put r) ⟩
           (do put s; [ k ⟨⟩ ]; put r) ≡⟨ _ ⇐ (put s) ⨾/ P⟨xs⟩ ⟨⟩ (ps ⟨⟩) ⟩
           (do put s; put r) ≡⟨ put-put s r (return ⟨⟩) ⟩
           put r ∎
           
         ; (op (inr `get , k) P⟨xs⟩) (_ , ps) → 
           [ op (inr `get , k) ] >> put r ≡⟨ cong (_>> put r) (syntactic-bind k Op⟦ inr `get ⟧) ⟩
           (do s ← get; [ k s ]) >> put r ≡⟨ assoc get _ _ ⟩
           (do s ← get; [ k s ]; put r) ≡⟨ s ⇐ get ⨾/ P⟨xs⟩ s (ps s) ⟩
           (do s ← get; put r) ≡⟨ get-nop (put r) ⟩
           put r ∎
         })
      s p 

open import FreeMonad.Theory using (DiscreteVars)

module _ (fv : DiscreteVars (FullTheory.𝒯 ℙ-theory)) (fa : ∀ O → ℰ (Arity O)) where
  open import Hoare.HElim ℙ-theory fv fa 

  parse-equality : ∀ t n →
    (do s ← get; put (print t ++ s); t′ ← parse-tree n; s′ ← get; put s′; return t′)
      ≡
    (do s ← get; put (print t ++ s); _  ← parse-tree n; s′ ← get; put s ; return t)
  parse-equality t n =
    let h = H-elim (λ { ((r , v′) , r′) → (r |≡| r′) |∧| (t |≡| v′) })
                   (λ { ((r , v′ ) , r′) → put r′ >> return v′ })
                   (λ { ((r , v′) , r′) → put r >> return t })
                   (λ { ((r , v′) , r′) (r≡r′ , t≡v′) → cong₂ (λ r v → put r >> return v) (∥rec∥ (isOfHLevelList 0 isSetChar _ _) sym r≡r′) (∥rec∥ (Discrete→isSet tree-eq _ _) sym t≡v′) })
                   _
                   (parse-put-print (print t) (parse-tree n) t (round-trip n t))
    in sym ( assoc get _ _
           ⨾ r ⇐ get ⨾/ assoc (put (print t ++ r)) _ _
           ⨾ _ ⇐ put (print t ++ r) ⨾/ assoc (parse-tree n) _ _
           ⨾ v′ ⇐ parse-tree n ⨾/ assoc get _ _)
     ⨾ h
     ⨾ assoc get _ _
     ⨾ r ⇐ get ⨾/ assoc (put (print t ++ r)) _ _
     ⨾ _ ⇐ put (print t ++ r) ⨾/ assoc (parse-tree n) _ _
     ⨾ v′ ⇐ parse-tree n ⨾/ assoc get _ _

  push-print-lhs : ∀ t n →
    (do s ← get; put (print t ++ s); t′ ← parse-tree n; s′ ← get; put s′; return t′)
      ≡
    (do s ← get; put (print t ++ s); parse-tree n)
  push-print-lhs t n = s ⇐ get ⨾/ _ ⇐ put (print t ++ s) ⨾/  ((t′ ⇐ parse-tree n ⨾/ get-put (return t′))) ⨾ >>=-idʳ (parse-tree n)

  push-print-rhs : ∀ t n → Total (do push (print t); parse-tree n) →
    (do s ← get; put (print t ++ s); _  ← parse-tree n; s′ ← get; put s ; return t)
      ≡
    return t
  push-print-rhs t n tot =

    (do s ← get
        put (print t ++ s)
        _ ← parse-tree n
        s′ ← get
        put s
        return t) ≡⟨ s ⇐ get ⨾/ _ ⇐ put (print t ++ s) ⨾/ _ ⇐ parse-tree n ⨾/ get-nop (put s >> return t) ⟩

    (do s ← get
        put (print t ++ s)
        _ ← parse-tree n
        put s
        return t) ≡˘⟨ get-get _ ⟩

    (do s ← get
        s′ ← get
        put (print t ++ s′)
        _ ← parse-tree n
        put s
        return t) ≡˘⟨ s ⇐ get ⨾/ assoc (push (print t) >> parse-tree n) _ _ ⨾ assoc (push (print t)) (const (parse-tree n)) (const (put s >> return t)) ⨾ assoc get _ _ ⟩

    (do s ← get
        ((push (print t) >> parse-tree n) >> put s)
        return t) ≡⟨ s ⇐ get ⨾/  cong (_>> return t) (Total-nop s (push (print t) >> parse-tree n) tot )  ⟩

    (do s ← get
        put s
        return t) ≡⟨ get-put (return t) ⟩

    return t ∎
    
  push-print-parse :
    ∀ t n
    → Total (do push (print t); parse-tree n) →
     (do push (print t); parse-tree n) ≡ return t
  push-print-parse t n tot = assoc get _ _
                           ⨾ sym (push-print-lhs t n)
                           ⨾ parse-equality t n
                           ⨾ push-print-rhs t n tot
