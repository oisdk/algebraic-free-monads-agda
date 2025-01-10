{-# OPTIONS --safe #-}

open import Prelude as P hiding ([_])
open import Data.Vec
open import Signatures
open import Cubical.Relation.Binary
open import FinitenessConditions
open import FreeMonad.PackagedTheory

--------------------------------------------------------------------------------
-- A Free monad, which is the syntax type quotiented by a theory
--------------------------------------------------------------------------------

module FreeMonad.Quotiented {ℓ} (theory : FullTheory ℓ) where

open FullTheory theory
open Signature 𝔽

private module Op-Display where
  open import FreeMonad.Syntax 𝔽 renaming (op to op′)

  op : ∃ o × (Arity o → Syntax A) → Syntax A
  op = op′

  open import FreeMonad.Relation 𝔽 𝒯

  [_] : Syntax A → Syntax A / _~ₜ_
  [_] = P.[_]

open P using ([_])

open import FreeMonad.Syntax 𝔽
open import FreeMonad.Theory ℓ 𝔽
open import FreeMonad.Relation 𝔽 𝒯 public

private variable xs ys zs : Syntax A
--------------------------------------------------------------------------------
-- The free monad is constructed by taking the quotient of the syntax over the
-- equivalence relation above.
--
-- Notice that the level is one higher than ℓ: this is the level of the context
-- variable. Because it's existentially quantified we need to go one level up.
-- 
-- However, we don't have any of the normal level issues that you might expect,
-- because we *don't* need to incrememnt the level of the paramater of the
-- computation. In other words, if ℓ = 0, then Term could have kind
-- Type₁ → Type₁. i.e. it is still an endofunctor, it can have values like
-- (Term (Term A)).
--
-- In fact, we could just have the context type be Fins or something.
-- Technically that wouldn't lose any expressive power (I think), but it would
-- be really annoying to work with.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- A pointwise relation on a vector can be extended to the ~ₜ relation
--------------------------------------------------------------------------------

module _ {o : Op} {B : Type b} where
  open SplitQuotientedChoiceAt {A = Arity o} {B = Syntax B} {_~_ = _~ₜ_} (finiteArity o) public

private variable o : Op

pointwiseₜ : {xs ys : Arity o → Syntax A}
           → xs ⟨ Pointwise _~ₜ_ ⟩ ys
           → op (o , xs) ~ₜ op (o , ys)
pointwiseₜ p = congₜ _ _ _ λ i → ~ₜ-effective _ _ (p i)

pointwise≡ : (xs ys : Arity o → Syntax A)
           → Pointwise _~ₜ_ xs ys →
           [ op (o , xs) ]ₜ ≡ [ op (o , ys) ]ₜ
pointwise≡ xs ys p = eq/ _ _ (pointwiseₜ p)

Opₜ⟦_⟧ : ∀ o → Term (Arity o)
Opₜ⟦ o ⟧ = [ Op⟦ o ⟧ ]

--------------------------------------------------------------------------------
-- We can implement the op operator on the quotiented free type
--------------------------------------------------------------------------------

private module Opₜ-Display {A : Type a} where

  module _ {o : Op} where
    cong-point :  (kₗ kᵣ : Arity o → Syntax A) →
                  (l~r : Pointwise _~ₜ_ kₗ kᵣ) →
                  [ op (o , kₗ) ]ₜ ≡ [ op (o , kᵣ) ]ₜ
    cong-point kₗ kᵣ l~r =
      eq/ (op (o , kₗ)) (op (o , kᵣ)) (congₜ o kₗ kᵣ λ i → ~ₜ-effective (kₗ i) (kᵣ i) (l~r i))
  opₜ : 𝔽 -Alg[ Term A ]
  opₜ (o , k~) = rec/ squash/ (λ k → [ op (o , k) ]) cong-point (trav k~)
  _ =
    opₜ ⦂ (∃ o × (Arity o → Syntax A / _~ₜ_) → Syntax A / _~ₜ_)
opₜ′ : (Arity o → Syntax A) → Term A
opₜ′ = [_] ∘ op ∘ _,_ _

opₜ : 𝔽 -Alg[ Term A ]
opₜ (Op , p) = rec/ squash/ opₜ′ pointwise≡ (trav p)

--------------------------------------------------------------------------------
-- Properties of opₜ
--------------------------------------------------------------------------------

opₜ-com-[] : (xs : Arity o → Syntax A) → opₜ (o , [_] ∘ xs) ≡ [ op (o , xs) ]
opₜ-com-[] xs = cong (rec/ squash/ opₜ′ pointwise≡) (un-trav xs)

interp-opₜ-com-[]  :  (k : A → Syntax B) (xs : Syntax A)
                   →  [ interp op k xs ] ≡ interp opₜ ([_] ∘ k) xs
interp-opₜ-com-[] k = interp-fusion [_]ₜ k (λ { (o , xs) → sym (opₜ-com-[] xs) })

--------------------------------------------------------------------------------
-- opₜ respects the theory: this means it can be used in interp, to implement
-- bind.
--------------------------------------------------------------------------------

opₜ-resp : (opₜ ⦂ 𝔽 -Alg[ Term A ]) Models 𝒯
opₜ-resp i t =
  let lhs ≐ rhs = 𝒯 .Theory.Eqns i .eqn t in 
  SplitQuotientedChoiceAt.elim~canonical (finiteVars _ _) _ (λ _ → squash/ _ _)
    λ k →
        interp opₜ ([_] ∘ k) lhs  ≡˘⟨ interp-opₜ-com-[] k lhs ⟩
        [ interp op k lhs ]       ≡⟨ eq/ _ _ (eqₜ i t k) ⟩
        [ interp op k rhs ]       ≡⟨ interp-opₜ-com-[] k rhs ⟩
        interp opₜ ([_] ∘ k) rhs ∎

infixl 4.5 _=<<_
infixr 4.5 _>>=_ _>>_

--------------------------------------------------------------------------------
-- Bind
--------------------------------------------------------------------------------

Op[_] : ∀ o → Term (Arity o)
Op[ o ] = [ op (o , var) ]

return : A → Term A
return x = [ var x ]

_=<<_ : (A → Term B) → Term A → Term B
_=<<_ k = interpₜ opₜ k opₜ-resp squash/

_>>=_ : Term A → (A → Term B) → Term B
xs >>= k = interpₜ opₜ k opₜ-resp squash/ xs

_>>_ : Term A → Term B → Term B
xs >> ys = xs >>= const ys

infixr 9 _<=<_
_<=<_ : (B → Term C) → (A → Term B) → A → Term C
(f <=< g) x = f =<< g x

infixl 9 _>=>_
_>=>_ :  (A → Term B) → (B → Term C) → A → Term C
_>=>_ = flip _<=<_

infixl 4.5 _<$>_
_<$>_ : (A → B) → Term A → Term B
f <$> xs = xs >>= return ∘ f

--------------------------------------------------------------------------------
-- Properties of bind
--------------------------------------------------------------------------------

module S = SyntaxBind

[⟪_⟫] : 𝔖𝔶𝔫𝔱𝔞𝔵 A (Term A) P → Term A
[⟪ 𝔖𝔶𝔫𝔱𝔞𝔵.var x ⟫] = return x
[⟪ 𝔖𝔶𝔫𝔱𝔞𝔵.op xs  _ ⟫] = opₜ xs

elimₜ-prop :  (P : Term A → Type p)  →
              (∀ x → isProp (P x)) →
              (ϕ : (xs : 𝔖𝔶𝔫𝔱𝔞𝔵 A (Term A) P) → P [⟪ xs ⟫]) →
              (xs : Term A) → P xs
elimₜ-prop {A = A} P prop ϕ = elimProp/ prop (elim-s (λ x → P [ x ]) Ψ)
  where
  Ψ : DepAlg A (λ x → P [ x ])
  Ψ (𝔖𝔶𝔫𝔱𝔞𝔵.var x) = ϕ (𝔖𝔶𝔫𝔱𝔞𝔵.var x)
  Ψ (𝔖𝔶𝔫𝔱𝔞𝔵.op (o , xs) P⟨xs⟩) = subst P (opₜ-com-[] xs) (ϕ (𝔖𝔶𝔫𝔱𝔞𝔵.op (o , λ i → [ xs i ]) P⟨xs⟩))

interpₜ-opₜ : {A B : Type ℓ}
  (ϕ : 𝔽 -Alg[ A ])
  (k : B → A)
  (resp : ϕ Models 𝒯)
  (set : isSet A)
  (o : Op)
  (xs : Arity o → Term B) →
  interpₜ ϕ k resp set (opₜ (o , xs)) ≡ ϕ (o , interpₜ ϕ k resp set ∘ xs)
interpₜ-opₜ ϕ k resp set o = elim~canonical _ (λ _ → set _ _) λ k′ → cong (interpₜ ϕ k resp set) (opₜ-com-[] k′)

syntactic-bind : (k : A → Syntax B) (xs : Syntax A)
            → [ xs S.>>= k ] ≡ [ xs ] >>= ([_] ∘ k)
syntactic-bind k = elim-s (λ xs → [ xs S.>>= k ] ≡ [ xs ] >>= [_] ∘ k) (alg k)
  where
  alg : (k : A → Syntax B) → Ψ[ xs ⦂ Syntax A ] ([ xs S.>>= k ] ≡ [ xs ] >>= [_] ∘ k)
  alg k (var x)       = refl
  alg k (op (o , xs) r) =
    [ op (o , xs) S.>>= k ]           ≡⟨⟩
    [ op (o , k S.<=< xs) ]           ≡˘⟨ opₜ-com-[] (k S.<=< xs) ⟩
    opₜ (o , [_] ∘ k S.<=< xs)        ≡⟨ cong (λ e → opₜ (o , e)) (funExt r) ⟩
    opₜ (o , interp opₜ ([_] ∘ k) ∘ xs) ≡⟨⟩
    interp opₜ ([_] ∘ k) (op (o , xs))  ≡⟨⟩
    [ op (o , xs) ] >>= [_] ∘ k ∎

algebraic : ∀ o (f : A → Term B) (xs : Arity o → Term A) →
               f =<< opₜ (o , xs) ≡ opₜ (o , f <=< xs)
algebraic o f xs =
  elimProp/
    {P = λ xs′ → xs′ ≡ trav xs
               → rec/ squash/ opₜ′ pointwise≡ xs′ >>= f ≡ opₜ (o , f <=< xs)}
    (λ _ → isProp→ (squash/ _ _)) lemma (trav xs) refl
  where
  lemma : ∀ xs′ → [ xs′ ] ≡ trav xs → f =<< opₜ′ xs′ ≡ opₜ (o , f <=< xs)
  lemma xs′ xp =
    opₜ′ xs′ >>= f                               ≡⟨⟩
    opₜ (o , f <=< dist [ xs′ ])         ≡⟨ cong (λ e → opₜ (o , f <=< dist e)) xp ⟩
    opₜ (o , f <=< dist (trav xs))  ≡⟨ cong (λ e → opₜ (o , f <=< e)) (funExt (dist∘trav xs)) ⟩
    opₜ (o , f <=< xs) ∎

assoc : (xs : Term C) (f : C → Term B) (g : B → Term A) →
              ((xs >>= f) >>= g) ≡ (xs >>= (f >=> g))
assoc xs f g =
  elimProp/
    {P = λ xs → ((xs >>= f) >>= g) ≡ (xs >>= (f >=> g))} 
    (λ _ → squash/ _ _)
    (elim-s (λ xs → interp opₜ f xs >>= g ≡ interp opₜ (f >=> g) xs) (alg f g))
    xs
  where
  alg : (f : C → Term B) (g : B → Term A)
      → Ψ[ xs ⦂ Syntax C ] (interp opₜ f xs >>= g ≡ interp opₜ (f >=> g) xs)
  alg f g (var x) = refl
  alg f g (op (o , xs) r) =
    interp opₜ f (op (o , xs)) >>= g    ≡⟨⟩
    opₜ (o , interp opₜ f ∘ xs) >>= g   ≡⟨ algebraic _ g _ ⟩
    opₜ (o , g <=< interp opₜ f ∘ xs)   ≡⟨⟩
    opₜ (o , g <=< interp opₜ f ∘ xs)   ≡⟨ cong (opₜ ∘ _,_ o) (funExt λ s → r s) ⟩
    opₜ (o , interp opₜ (f >=> g) ∘ xs) ≡⟨⟩
    interp opₜ (f >=> g) (op (o , xs)) ∎

>>=-idʳ : (xs : Term A) → xs >>= ([_] ∘ var) ≡ xs
>>=-idʳ =
  elimProp/
    (λ _ → squash/ _ _)
    (λ xs → sym (syntactic-bind var xs) ⨾ cong [_] (interp-id xs))

>>=-idˡ : (x : A) (k : A → Term B)  → [ var x ] >>= k ≡ k x
>>=-idˡ _ _ = refl

<$>-id : (xs : Term A) → id <$> xs ≡ xs
<$>-id = >>=-idʳ

<$>-comp : (f : B → C) (g : A → B) (xs : Term A) → f <$> (g <$> xs) ≡ (f ∘ g) <$> xs
<$>-comp f g xs = assoc xs _ _

infixr 2 following
following : (v : Term A) {k₁ k₂ : A → Term B} (pr : (x : A) → k₁ x ≡ k₂ x) → v >>= k₁ ≡ v >>= k₂
following v pr = cong (v >>=_) (funExt pr)

syntax following v (λ x → e) = x ⇐ v ⨾/ e

join : Term (Term A) → Term A
join t = t >>= (λ x → x)

-- Somehow the following function is very slow to type check, so we make it abstract.
abstract
  >>=-join-eq : (s : Term A) (f : A → Term B) → (s >>= f) ≡ join (f <$> s)
  >>=-join-eq s f
    = (s >>= f)                           ≡⟨⟩
      (s >>= ((return ∘ f) >=> (λ x → x)))   ≡˘⟨ assoc s _ _ ⟩
      (s >>= (return ∘ f)) >>= (λ x → x)     ≡⟨⟩
      (f <$> s) >>= (λ x → x)             ≡⟨⟩
      join (f <$> s)                      ∎

<$>-comm : (s : Syntax A) (f : A → B) → f <$> [ s ] ≡ [ f S.<$> s ]
<$>-comm s f = sym (syntactic-bind (var ∘ f) s)

>>=-join-comm : (s : Syntax A) (f : A → Term B) → [ s ] >>= f ≡ join [ f S.<$> s ]
>>=-join-comm s f = >>=-join-eq [ s ] f ⨾ (λ i → join (<$>-comm s f i))
