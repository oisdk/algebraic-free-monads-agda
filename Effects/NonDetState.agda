{-# OPTIONS --safe --lossy-unification #-}

open import Prelude
open import FinitenessConditions
open import Signatures

module Effects.NonDetState
  (S : Type)
  (choice : SplitQuotientedChoiceω S)
  (set : isSet S)
  where

import Effects.NonDet as ℕ𝔻
import Effects.State S choice set as 𝕊
open import FreeMonad.Combinations.Tensor ℕ𝔻.ℕ𝔻-theory 𝕊.𝕊-theory

open import FreeMonad.Quotiented combinedTheory


import FreeMonad.Syntax as Synt
open Synt (ℕ𝔻.ℕ𝔻 ⊞ 𝕊.𝕊) using (Op⟦_⟧)
open Signature (ℕ𝔻.ℕ𝔻 ⊞ 𝕊.𝕊)
open ℕ𝔻.NonDet.Op

put : S → Term ⊤
put s = [ inj₂ (𝕊.Synt.put s) ]

get : Term (S)
get = [ inj₂ 𝕊.Synt.get ]

fail : Term A
fail = [ Synt.op (inl `fail , absurd) ]


infixl 5 _<|>_
_<|>_ : Term A → Term A → Term A
xs <|> ys = opₜ (inl `<|> , bool ys xs)

until : ℕ → Term Bool → Term ⊤ → Term ⊤
until zero    c t = fail
until (suc n) c t = c >>= bool (t >> until n c t) (return tt)

guard : Bool → Term ⊤
guard = bool fail (return tt)

open import Data.Nat.Order using () renaming (_<ᵇ_ to _<_)
open import Data.Nat.Properties using (_+_)

<|>-alg : (p q : Term A) (k : A → Term B) → ((p <|> q) >>= k) ≡ ((p >>= k) <|> (q >>= k))
<|>-alg p q k = algebraic (inl `<|>) k (bool q p)

<|>-idem : (x : Term A) → x <|> x ≡ x
<|>-idem = elimProp/ (λ _ → squash/ _ _ )
  λ x → cong ([_] ∘ Synt.op ∘ _,_ (inl `<|>)) (funExt (bool refl refl)) ⨾ eq/ _ _ (eqₜ (inl (inl ℕ𝔻.Synt.idem)) tt (const x))

<|>-assoc : (x y z : Term A) → (x <|> y) <|> z ≡ x <|> (y <|> z)
<|>-assoc = elimProp3/ (λ _ _ _ → squash/ _ _ )
  λ x y z →
    let h = eq/ _ _ (eqₜ (inl (inl ℕ𝔻.Synt.assoc)) tt λ { zero → z ; (suc zero) → y ; _ → x })
    in cong ([_] ∘ Synt.op ∘ _,_ (inl `<|>)) (funExt (bool refl (cong (Synt.op ∘ _,_ (inl `<|>)) (funExt (bool refl refl)))))
     ⨾ sym h
     ⨾ cong ([_] ∘ Synt.op ∘ _,_ (inl `<|>)) (funExt (bool (cong (Synt.op ∘ _,_ (inl `<|>)) (funExt (bool refl refl))) refl))

<|>-comm : (x y : Term A) → x <|> y ≡ y <|> x
<|>-comm = elimProp2/ (λ _ _ → squash/ _ _ )
  λ x y →
    let h = eq/ _ _ (eqₜ (inl (inl ℕ𝔻.Synt.comm)) tt λ { zero → y ; _ → x })
    in cong ([_] ∘ Synt.op ∘ _,_ (inl `<|>)) (funExt (bool refl refl))
     ⨾ h
     ⨾ cong ([_] ∘ Synt.op ∘ _,_ (inl `<|>)) (funExt (bool refl refl))

side : Term Bool
side = Opₜ⟦ inl `<|> ⟧



open import Hoare.Definition combinedTheory
open import Hoare.Lemmas     combinedTheory
open import Hoare.Calculus   combinedTheory

comm-<|>-op : ∀ Oₛ (k : Arity (inr Oₛ) × Arity (inl `<|>) → Term A) → (do s ← Opₜ⟦ inr Oₛ ⟧; n ← side; k (s , n)) ≡ (do n ← side; s ← Opₜ⟦ inr Oₛ ⟧; k (s , n))
comm-<|>-op Oₛ =
  SplitQuotientedChoiceAt.elim~canonical
    (quotientedChoiceProd (𝕊.finiteOps Oₛ) quotientedChoiceBool)
    _
    (λ _ → squash/ _ _)
    λ k → sym (s ⇐ Opₜ⟦ inr Oₛ ⟧ ⨾/ syntactic-bind (λ n → k (s , n)) Op⟦ inl `<|> ⟧)
        ⨾ sym (syntactic-bind (λ s → Synt.op (inl `<|> , λ n → k (s , n))) (Op⟦ inr Oₛ ⟧))
        ⨾ sym ( eq/ _ _ (commutes′ `<|> Oₛ (flip (curry k))) )
        ⨾ syntactic-bind (λ n → Synt.op (inr Oₛ , λ s → k (s , n)))  Op⟦ inl `<|> ⟧
        ⨾ (n ⇐ side ⨾/ (syntactic-bind (λ s → k (s , n)) Op⟦ inr Oₛ ⟧))

fail-exit : (k : A → Term B) → (fail >>= k) ≡ fail
fail-exit k = 
  fail >>= k ≡⟨ algebraic (inl `fail) k absurd ⟩
  opₜ (inl `fail , k ∘ absurd) ≡⟨ cong {x = k ∘ absurd} {y = [_] ∘ absurd} (opₜ ∘ _,_ (inl `fail)) (funExt (λ ())) ⟩
  opₜ (inl `fail , [_] ∘ absurd) ≡⟨ opₜ-com-[] absurd ⟩
  [ Synt.op (inl `fail , absurd) ] ≡⟨⟩
  fail ∎

<|>-comm-dupe : (k : Bool → Bool → Term A) → (do s₁ ← side; s₂ ← side; k s₁ s₂) ≡ (do s₁ ← side; s₂ ← side; k s₂ s₁)
<|>-comm-dupe k =
  (k true true <|> k true false) <|> (k false true <|> k false false) ≡⟨ <|>-assoc (k true true) (k true false) (k false true <|> k false false) ⨾ cong (k true true <|>_) (sym (<|>-assoc (k true false) (k false true) (k false false))) ⟩
  k true true <|> ((k true false <|> k false true) <|> k false false) ≡⟨ cong (λ e → k true true <|> (e <|> k false false)) (<|>-comm (k true false) (k false true)) ⟩
  k true true <|> ((k false true <|> k true false) <|> k false false) ≡˘⟨ <|>-assoc (k true true) (k false true) (k true false <|> k false false) ⨾ cong (k true true <|>_) (sym (<|>-assoc (k false true) (k true false) (k false false))) ⟩
  (k true true <|> k false true) <|> (k true false <|> k false false) ∎

sef′-<|> : (k : A → Bool → Term B) (p : Term A) → 
           (do x ← p ; s ← side ; k x s) ≡ (do s ← side ; x ← p ; k x s)
sef′-<|> k =
  elimₜ-prop
    _
    (λ _ → squash/ _ _)
    λ { (Synt.var x) → refl
      ; (Synt.op (Oᵢ , xs) P⟨xs⟩) → algebraic Oᵢ _ _ ⨾ (i ⇐ Opₜ⟦ Oᵢ ⟧ ⨾/ P⟨xs⟩ i) ⨾ lemma Oᵢ xs k P⟨xs⟩ ⨾ s ⇐ side ⨾/ (sym (algebraic Oᵢ (λ x → k x s) xs))
      }
  where
  lemma : ∀ Oᵢ (xs : Arity Oᵢ → Term A) (k : A → Bool → Term B)
        → (∀ i → (xs i >>= λ x → side >>= k x) ≡ side >>= (λ s → xs i >>= λ x → k x s))
        → (do i ← Opₜ⟦ Oᵢ ⟧; s ← side; x ← xs i; k x s) ≡ (do s ← side ; i ← Opₜ⟦ Oᵢ ⟧; x ← xs i; k x s)
  lemma (inl `<|>)  xs k x = <|>-comm-dupe (λ s₁ s₂ → xs s₁ >>= λ x → k x s₂)

  lemma (inr Oₛ)    xs k x = comm-<|>-op Oₛ (λ { (i , s) → xs i >>= flip k s })
  lemma (inl `fail) xs k x =

    (do f ← Opₜ⟦ inl `fail ⟧
        s ← side
        x ← xs f
        k x s) ≡⟨ fail-exit (λ f → side >>= λ s → xs f >>= flip k s) ⟩

    fail ≡˘⟨ <|>-idem fail ⟩

    (do s ← side
        fail)  ≡˘⟨ s ⇐ side ⨾/ fail-exit (xs >=> flip k s)  ⟩

    (do s ← side
        f ← Opₜ⟦ inl `fail ⟧
        x ← xs f
        k x s) ∎
       

sef-<|> : (p : Term A) (q r : A → Term B) → (p >>= (λ x → q x <|> r x)) ≡ ((p >>= q) <|> (p >>= r))
sef-<|> p q r = sef′-<|> (λ x s → bool (r x) (q x) s) p


module _ where
  open import Truth.Definition ℓzero
  open import Truth.Combinators {ℓzero}
  open import Truth using (|→|-id)

  guard-hoare : ∀ p → ⟅⟆ guard p ⟅ return (|T| p) ⟆
  guard-hoare false .proof k = refl
  guard-hoare true  .proof k = cong (k tt) (|→|-id _)

  fail-absurd : (ϕ : A → Term Ω) →
    ⟅⟆ x ← fail ⟅ ϕ x ⟆
  fail-absurd ϕ .proof k = refl

open import Truth

<|>-conj : {A : Type a}
     →                 (ϕ : Term (Ω a)) →
                       (ψ : A → Term (Ω a))
     →                              (p q : Term A) →
  ⟅ ϕ ⟆ x ← p        ⟅ ψ x ⟆ →
  ⟅ ϕ ⟆ x ← q        ⟅ ψ x ⟆ →
  ⟅ ϕ ⟆ x ← p <|> q  ⟅ ψ x ⟆
<|>-conj ϕ ψ p q lhs rhs .proof k =
  (do a ← ϕ
      x ← (p <|> q)
      b ← ψ x
      k x (a |→| b)) ≡⟨ a ⇐ ϕ ⨾/ <|>-alg p q _ ⟩

  (do a ← ϕ;
        (do x ← p
            b ← ψ x
            k x (a |→| b))
          <|>
        (do x ← q
            b ← ψ x
            k x (a |→| b)))

          ≡⟨ sef-<|> ϕ _ _ ⟩

  (do a ← ϕ
      x ← p
      b ← ψ x
      k x (a |→| b))
    <|>
  (do a ← ϕ
      x ← q
      b ← ψ x
      k x (a |→| b))
          ≡⟨ cong₂ _<|>_ (lhs .proof k) (rhs .proof k) ⟩

  (do a ← ϕ
      x ← p
      b ← ψ x
      k x True)
    <|>
  (do a ← ϕ
      x ← q
      b ← ψ x
      k x True)
        ≡˘⟨ sef-<|> ϕ _ _ ⟩

  (do a ← ϕ;
        (do x ← p
            b ← ψ x
            k x True)
          <|>
        (do x ← q
            b ← ψ x
            k x True))
          ≡˘⟨ a ⇐ ϕ ⨾/ <|>-alg p q _ ⟩

  (do a ← ϕ
      x ← (p <|> q)
      b ← ψ x
      k x True) ∎
