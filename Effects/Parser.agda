{-# OPTIONS --lossy-unification --safe #-}

open import Prelude renaming (tt to ⟨⟩)
open import Signatures
open import FinitenessConditions
open import FreeMonad.PackagedTheory

open import Data.String.Properties renaming (discreteChar to _≟_)

module Effects.Parser
  (choiceString : SplitQuotientedChoiceω String)
  where

open import Cubical.Data.List.Properties using (isOfHLevelList)

open import Data.Tree
import Effects.NonDet as ℕ𝔻
import Effects.State String choiceString isSetString as 𝕊
open import FreeMonad.Combinations.Tensor ℕ𝔻.ℕ𝔻-theory 𝕊.𝕊-theory
  renaming (combinedTheory to ℙ-theory) public

open 𝕊 using (`get; `put)
open ℕ𝔻.NonDet using (`<|>; `fail)

module SyntaxExamples where
  open import FreeMonad.Syntax (ℕ𝔻.ℕ𝔻 ⊞ 𝕊.𝕊)
  open SyntaxBind

  put : String → Syntax ⊤
  put s = op (inr (`put s) , var)
  get : Syntax String
  get = op (inr `get , var)
  fail : Syntax A
  fail = op (inl `fail , absurd)
  infixl 6 _<|>_
  _<|>_ : Syntax A → Syntax A → Syntax A
  x <|> y = op (inl `<|> , bool x y)

  guard : Bool → Syntax ⊤
  guard = bool fail (var ⟨⟩)

  eof : Syntax ⊤
  eof = do s ← get; guard (null s)
  any-char : Syntax Char
  any-char = do c ∷ cs ← get
                  where [] → fail
                put cs
                return c
  char : Char → Syntax ⊤
  char c₁ = do c₂ ← any-char
               if (does (c₁ ≟ c₂))
                 then return ⟨⟩
                 else fail

open import FreeMonad.Quotiented ℙ-theory public

import FreeMonad.Syntax as Synt
open Synt (ℕ𝔻.ℕ𝔻 ⊞ 𝕊.𝕊) using (Op⟦_⟧; op; var)
open Signature (ℕ𝔻.ℕ𝔻 ⊞ 𝕊.𝕊)
open ℕ𝔻.NonDet.Op

private module DisplayPut where
  put : String → Term ⊤
  put s = [ op (inr (`put s) , var) ]

put : String → Term ⊤
put s = [ inj₂ (𝕊.Synt.put s) ]

get : Term String
get = [ inj₂ 𝕊.Synt.get ]

fail : Term A
fail = [ op (inl `fail , absurd) ]

infixl 6 _<|>_
_<|>_ : Term A → Term A → Term A
x <|> y = opₜ (inl `<|> , λ i → if i then y else x)
guard : Bool → Term ⊤
guard = bool fail (return ⟨⟩)

eof : Term ⊤
eof = do s ← get; guard (null s)

any-char : Term Char
any-char = get >>= maybe fail (λ { (c , cs) → put cs >> return c }) ∘ uncons

char : Char → Term ⊤
char c₁ = do c₂ ← any-char
             guard (does (c₁ ≟ c₂))

modify : (String → String) → Term ⊤
modify f = do s ← get; put (f s)

push : String → Term ⊤
push s = modify (s ++_)

fail->>= : (k : A → Term B) → fail >>= k ≡ fail
fail->>= k =
  (fail >>= k) ≡⟨ cong {x = k ∘ absurd} (opₜ ∘ _,_ (inl `fail )) (funExt λ () ) ⟩
  opₜ (inl `fail , [_] ∘ absurd) ≡⟨ opₜ-com-[] absurd ⟩
  [ op (inl `fail , absurd) ] ≡⟨ cong ([_] ∘ op ∘ _,_ (inl `fail)) (funExt λ ()) ⟩
  fail ∎

<|>-assoc : (x y z : Term A) → (x <|> y) <|> z ≡ x <|> (y <|> z)
<|>-assoc = elimProp3/ (λ _ _ _ → squash/ _ _)
  λ x y z →
    let h = eq/ _ _ (eqₜ (inl (inl ℕ𝔻.Synt.assoc)) ⟨⟩ λ { zero → x ; (suc zero) → y ; _ → z })
    in cong ([_] ∘ Synt.op ∘ _,_ (inl `<|>)) (funExt (bool (cong (op ∘ _,_ (inl `<|>)) (funExt (bool refl refl))) refl))
     ⨾ h
     ⨾ cong ([_] ∘ Synt.op ∘ _,_ (inl `<|>)) (funExt (bool refl (cong (op ∘ _,_ (inl `<|>)) (funExt (bool refl refl)))))

<|>-idem : (x : Term A) → x <|> x ≡ x
<|>-idem =
  elimProp/
    (λ _ → squash/ _ _)
    λ x → cong ([_] ∘ Synt.op ∘ _,_ (inl `<|>)) (funExt (bool refl refl))
        ⨾ eq/ _ _  (eqₜ (inl (inl ℕ𝔻.Synt.idem)) ⟨⟩  λ _ → x)

open import Effects.NonDetState String choiceString isSetString as NDS using (sef-<|>; fail-absurd; <|>-conj)

module _ {A : Type} where
  <|>-distrib :
    ∀ (c : Char) (p q : Term A) → (do char c; p) <|> (do char c; q) ≡ (do char c; p <|> q)
  <|>-distrib c x y = sym (sef-<|> (char c) (const y) (const x))

open import Truth.Definition ℓzero
open import Truth.Combinators {ℓzero}
open import Truth using (_|≡|_)

open import Hoare.Definition ℙ-theory
open import Hoare.Calculus ℙ-theory
open import Hoare.Lemmas ℙ-theory

fail-anything :
  (ψ : Term Ω) → ⟅⟆ fail ⟅ ψ ⟆
fail-anything ψ = fail-absurd (const ψ)

module _ {A : Type} {ϕ : Term Ω} {p q : Term A} {ψ : A → Term Ω} where
  infixl 6 _⟨<|>⟩_
  _⟨<|>⟩_ :
    (⟅ ϕ ⟆ x ← p ⟅ ψ x ⟆) → (⟅ ϕ ⟆ x ← q ⟅ ψ x ⟆) → (⟅ ϕ ⟆ x ← p <|> q ⟅ ψ x ⟆)
  lhs ⟨<|>⟩ rhs = <|>-conj ϕ ψ q p rhs lhs


remaining : String → Term Ω
remaining s₁ = do s₂ ← get
                  return (s₁ |≡| s₂)
no-input : Term A → Type-
no-input p =
  ∀ s → ⟅ remaining s ⟆ _ ← p ⟅ remaining s ⟆
module _ {A : Type} where
  _∈_↦_ : String → Term A → A → Type _
  s ∈ p ↦ v = ∀ r → ⟅ remaining (s ++ r) ⟆ v′ ← p ⟅ return (v |≡| v′) ⟨∧⟩ remaining r ⟆

open import Truth.Logic
open import Effects.NonDet using (ℕ𝔻-theory; term-iso)
open import Effects.State.Tensor String choiceString isSetString ℕ𝔻-theory as ST using (stateT-iso)
open import Data.Set hiding (ψ)

put-put : ∀ s₁ s₂ (k : Term A) → (do put s₁; put s₂; k) ≡ (do put s₂; k)
put-put s₁ s₂ k = cong (λ p → do p ; k) (eq/ _ _ (lawₜ (inl (inr 𝕊.Synt.put-put)) (s₁ , s₂)))

get-put : ∀ (k : Term A) → (do s ← get; put s; k) ≡ k
get-put k = cong (_>> k) (eq/ _ _ (lawₜ (inl (inr 𝕊.Synt.get-put)) _))

put-get : ∀ s (k : String → Term A) → (do put s; s′ ← get; k s′) ≡ (do put s; k s)
put-get s k = cong (λ p → do r ← p; k r) (eq/ _ _ (lawₜ (inl (inr 𝕊.Synt.put-get)) s))

get-put-get : (k : String → Term A) → (do s ← get; put s; k s) ≡ (do s ← get; k s)
get-put-get k = sym (s ⇐ get ⨾/ put-get s k) ⨾ get-put (get >>= k)

get-nop : (k : Term A) → (get >> k) ≡ k
get-nop k = sym (get-put-get (λ _ → k)) ⨾ get-put k

get-get : ∀  (k : String → String → Term B) →
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

module _ {A : Type} where
  parser-iso : Term A ⇔ (String → 𝒦 (A × String))
  parser-iso .fun = _∘_ (term-iso .fun) ∘ stateT-iso .fun
  parser-iso .inv = stateT-iso .inv ∘ (_∘_ (term-iso .inv))
  parser-iso .rightInv x = cong (_∘_ (term-iso .fun) ) (stateT-iso .rightInv _) ⨾ funExt (term-iso .rightInv ∘′ x)
  parser-iso .leftInv x = cong (stateT-iso .inv) (funExt λ s → term-iso .leftInv _) ⨾ stateT-iso .leftInv x

sef-rem : ∀ s → SEF a (remaining s)
sef-rem s k = assoc get _ _ ⨾ get-nop k

det-rem : ∀ s → DET a (remaining s)
det-rem s k =
  (do x ← remaining s ; y ← remaining s ; k x y) ≡⟨ assoc get _ _ ⟩
  (do s₁ ← get; y ← remaining s ; k (s |≡| s₁) y) ≡⟨ s₁ ⇐ get ⨾/ assoc get _ _ ⟩
  (do s₁ ← get; s₂ ← get; k (s |≡| s₁) (s |≡| s₂)) ≡⟨ get-get _ ⟩
  (do s₁ ← get; k (s |≡| s₁) (s |≡| s₁)) ≡˘⟨ s₁ ⇐ get ⨾/ get-nop _ ⟩
  (do s₁ ← get; s₂ ← get; k (s |≡| s₁) (s |≡| s₁)) ≡˘⟨  s₁ ⇐ get ⨾/ assoc get _ _ ⟩
  (do s₁ ← get; remaining s; k (s |≡| s₁) (s |≡| s₁)) ≡˘⟨ assoc get _ _ ⟩
  (do x ← remaining s ; remaining s ; k x x) ∎

⟨remaining⟩ : String → Assertion ℓzero
⟨remaining⟩ s .fst = remaining s
⟨remaining⟩ s .snd .fst = sef-rem s
⟨remaining⟩ s .snd .snd = det-rem s

put-remaining : ∀ s → ⟅⟆ _ ← put s ⟅ remaining s ⟆
put-remaining s .proof k =
  (do put s
      b ← remaining s
      k ⟨⟩ (True |→| b)) ≡⟨ cong (put s >>_) (assoc get _ _) ⟩

  (do put s
      s′ ← get
      k ⟨⟩ (True |→| (s |≡| s′))) ≡⟨ put-get s _ ⟩

  (do put s
      k ⟨⟩ (True |→| (s |≡| s))) ≡⟨ _ ⇐ put s ⨾/ cong (k ⟨⟩) (proves λ _ → ∣ refl ∣) ⟩

  (do put s
      k ⟨⟩ True) ≡˘⟨ _ ⇐ put s ⨾/ sef-rem s (k ⟨⟩ True)  ⟩

  (do put s
      remaining s
      k ⟨⟩ True) ∎

head-def : A → List A → A
head-def x [] = x
head-def _ (x ∷ _) = x

parse-char-lemma : ∀ (k : ⊤ → Ω → Term A) (c₁ c₂ c₃ : Char) (s₁ s₂ : String) (eq : Dec (c₂ ≡ c₃)) →

        (do put s₂
            guard (does eq)
            s₃ ← get
            k ⟨⟩ ((c₁ List.∷ s₁) |≡| (c₃ ∷ s₂) |→| ((c₁ |≡| c₂) |∧| (s₁ |≡| s₃)))) ≡

        (do put s₂
            guard (does eq)
            s₃ ← get
            k ⟨⟩ True)
parse-char-lemma k c₁ c₂ c₃ s₁ s₂ (no  c₁≢c₂) =
  cong (put s₂ >>_) (fail->>= {A = ⊤} (λ _ → get >>= λ s₃ → k ⟨⟩ ((c₁ List.∷ s₁) |≡| (c₃ List.∷ s₂) |→| ((c₁ |≡| c₂) |∧| (s₁ |≡| s₃)))) ⨾ sym (fail->>= {A = ⊤} (λ _ → get >>= λ s₃ → k ⟨⟩ True))) 
parse-char-lemma k c₁ c₂ c₃ s₁ s₂ (yes c₁≡c₂) =
        (do put s₂
            s₃ ← get
            k ⟨⟩ ((c₁ List.∷ s₁) |≡| (c₃ ∷ s₂) |→| ((c₁ |≡| c₂) |∧| (s₁ |≡| s₃)))) ≡⟨ put-get s₂ _ ⟩

        (do put s₂
            k ⟨⟩ ((c₁ List.∷ s₁) |≡| (c₃ ∷ s₂) |→| ((c₁ |≡| c₂) |∧| (s₁ |≡| s₂)))) ≡⟨ cong (λ e → do put s₂; k ⟨⟩ e) ((λ _ → _) iff λ _ → ∥rec∥ (isProp× squash squash) λ p → ∣ cong (head-def c₁) p ⨾ sym c₁≡c₂ ∣ , ∣ cong tail p ∣ ) ⟩

        (do put s₂
            k ⟨⟩ True) ≡˘⟨ put-get s₂ _ ⟩

        (do put s₂
            s₃ ← get
            k ⟨⟩ True) ∎

parse-char :
  ∀ c₁ c₂ s → ⟅ remaining (c₁ ∷ s) ⟆ char c₂ ⟅ return (c₁ |≡| c₂) ⟨∧⟩ remaining s ⟆
parse-char c₁ c₂ s .proof k =

  (do a ← remaining (c₁ ∷ s)
      char c₂
      b ← return (c₁ |≡| c₂) ⟨∧⟩ remaining s
      k ⟨⟩ (a |→| b))

      ≡⟨ assoc get _ _ ⟩

  (do s₁ ← get
      char c₂
      b ← return (c₁ |≡| c₂) ⟨∧⟩ remaining s
      k ⟨⟩ ((c₁ ∷ s) |≡| s₁ |→| b))

      ≡⟨ s₁ ⇐ get ⨾/ _ ⇐ char c₂ ⨾/ assoc (return (c₁ |≡| c₂)) (λ b′ → remaining s >>= λ b″ → return (b′ |∧| b″) ) _ ⨾ assoc (remaining s) _ _ ⨾ assoc get _ _  ⟩

  (do s₁ ← get
      char c₂
      s₂ ← get
      k ⟨⟩ ((c₁ ∷ s) |≡| s₁ |→| ((c₁ |≡| c₂) |∧| (s |≡| s₂))))

      ≡⟨⟩

  (do s₁ ← get
      (get >>= maybe fail (λ { (c , cs) → put cs >> return c }) ∘ uncons) >>= (guard ∘ does ∘′ (c₂ ≟_))
      s₂ ← get
      k ⟨⟩ ((c₁ ∷ s) |≡| s₁ |→| ((c₁ |≡| c₂) |∧| (s |≡| s₂))))

      ≡⟨ s₁ ⇐ get ⨾/ assoc (get >>= maybe fail (λ { (c , cs) → put cs >> return c }) ∘ uncons) _ _ ⟩

  (do s₁ ← get
      c₃ ← (get >>= maybe fail (λ { (c , cs) → put cs >> return c }) ∘ uncons)
      guard (does (c₂ ≟ c₃))
      s₂ ← get
      k ⟨⟩ ((c₁ ∷ s) |≡| s₁ |→| ((c₁ |≡| c₂) |∧| (s |≡| s₂))))

      ≡⟨ s₁ ⇐ get ⨾/ assoc get _ _ ⟩

  (do s₁ ← get
      s₃ ← get
      c₃ ← maybe fail (λ { (c , cs) → put cs >> return c }) (uncons s₃)
      guard (does (c₂ ≟ c₃))
      s₂ ← get
      k ⟨⟩ ((c₁ ∷ s) |≡| s₁ |→| ((c₁ |≡| c₂) |∧| (s |≡| s₂))))

      ≡⟨ get-get _ ⟩

  (do s₁ ← get
      c₃ ← maybe fail (λ { (c , cs) → put cs >> return c }) (uncons s₁)
      guard (does (c₂ ≟ c₃))
      s₂ ← get
      k ⟨⟩ ((c₁ ∷ s) |≡| s₁ |→| ((c₁ |≡| c₂) |∧| (s |≡| s₂))))

      ≡⟨ cong (get >>=_) (funExt
          λ { [] → fail->>= (λ c₃ → do guard (does (c₂ ≟ c₃)); s₂ ← get; k ⟨⟩ ((c₁ ∷ s) |≡| [] |→| ((c₁ |≡| c₂) |∧| (s |≡| s₂) ))) ⨾ sym (fail->>= (λ c₃ → do guard (does (c₂ ≟ c₃)); s₂ ← get; k ⟨⟩ True))
            ; (c₃ ∷ cs) → parse-char-lemma k c₁ c₂ c₃ _ _ (c₂ ≟ c₃)
            }) ⟩

  (do s₁ ← get
      c₃ ← maybe fail (λ { (c , cs) → put cs >> return c }) (uncons s₁)
      guard (does (c₂ ≟ c₃))
      s₂ ← get
      k ⟨⟩ True) ≡˘⟨ assoc get _ _
                  ⨾ (s₁ ⇐ get ⨾/ _ ⇐ char c₂ ⨾/ assoc (return (c₁ |≡| c₂)) (λ b′ → remaining s >>= λ b″ → return (b′ |∧| b″) ) _ ⨾ assoc (remaining s) _ _ ⨾ assoc get _ _)
                  ⨾ (s₁ ⇐ get ⨾/ assoc (get >>= maybe fail (λ { (c , cs) → put cs >> return c }) ∘ uncons) _ _)
                  ⨾ (s₁ ⇐ get ⨾/ assoc get _ _)
                  ⨾ get-get _
                  ⟩

  (do a ← remaining (c₁ ∷ s)
      char c₂
      b ← return (c₁ |≡| c₂) ⟨∧⟩ remaining s
      k ⟨⟩ True) ∎

module _ {A : Type} (Ψ : A → Assertion 0) where
  private ψ = fst ∘ Ψ

  char-ne : ∀  c₁ c₂ s (t : Term A) → c₁ ≢ c₂ → ⟅ remaining (c₁ ∷ s) ⟆ x ← char c₂ >> t ⟅ ψ x ⟆
  char-ne c₁ c₂ s t c₁≢c₂ =
    seq′ (⟨remaining⟩ (c₁ ∷ s))
         (λ _ → (return (c₁ |≡| c₂) ⟨∧⟩ remaining s) , sef-<$> _ _ (⟨remaining⟩ s .snd .fst) , det-<$> _ _ (⟨remaining⟩ s .snd .snd))
         Ψ
         (parse-char c₁ c₂ s)
         (λ _ → ≡⟅∙⟆ (sym (cong (_⟨∧⟩ remaining s) (cong return (disproves (∥rec∥ (λ ()) c₁≢c₂))) ⨾ False⟨∧⟩ (remaining s) (sef-rem s) )) (False⟅→⟆ t ψ))

from-dec-false : (d : Dec A) → T (! (does d)) → ¬ A
from-dec-false (no ¬p) t = ¬p
