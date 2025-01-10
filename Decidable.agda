{-# OPTIONS --safe #-}

module Decidable where

open import Cubical.Relation.Nullary
  using ( Stable )
  public
open import Cubical.Relation.Nullary.Properties
  using  ( Dec→Stable
         ; Discrete→isSet
         ; isPropDec
         )
  public
open import Cubical.Relation.Nullary.Base
  using
    ( Dec
    ; yes
    ; no
    ; Discrete
    )
  public


open import Level
open import Data.Bool
open import Path
open import Inspect
open import Data.Unit

T? : ∀ d → Dec (T d)
T? = bool (no λ x → x) (yes tt)

open import HLevels using (isProp; isPropΠ)

isProp⇒Discrete : isProp A → Discrete A
isProp⇒Discrete p x y = yes (p x y)

isPropDiscrete : isProp (Discrete A)
isPropDiscrete _≟_ = isPropΠ (λ x → isPropΠ (λ y → isPropDec (Discrete→isSet _≟_ _ _))) _≟_

open import Data.Empty

infixr 2 dec
dec : (A → B) → (¬ A → B) → Dec A →  B
dec t f (yes p) = t p
dec t f (no ¬p) = f ¬p

syntax dec (λ p → t) (λ ¬p → f) d = If d Then p ⇒ t Else ¬p ⇒ f

does : Dec A → Bool
does d = If d Then _ ⇒ true Else _ ⇒ false

from-does : (d : Dec A) → T (does d) → A
from-does (yes p) _ = p

map-dec : (A → B) → (¬ A → ¬ B) → Dec A → Dec B
map-dec t f d = If d Then p ⇒ yes (t p) Else ¬p ⇒ no (f ¬p)

open import Function
open import Data.Sigma

iff-dec : (A ↔ B) → Dec A → Dec B
iff-dec (f , f⁻) = map-dec f λ ¬A B → ¬A (f⁻ B)

record EqAlg (A : Type a) : Type a where
  field
    _≡ᴮ_ : A → A → Bool
    sound : ∀ x y → T (x ≡ᴮ y) → x ≡ y
    complete : ∀ x → T (x ≡ᴮ x)

  from-bool-eq : Discrete A
  from-bool-eq x y =
    map-dec
      (sound x y)
      (λ x≢ᴮy x≡y → x≢ᴮy (subst (λ z → T (x ≡ᴮ z)) x≡y (complete x)))
      (T? (x ≡ᴮ y))
open EqAlg using (from-bool-eq) public

open import HITs.PropositionalTruncation

dec-trunc : Dec A → Dec ∥ A ∥
dec-trunc = map-dec ∣_∣ (∥rec∥ (λ ()))
    
dec-untrunc : Dec A → ∥ A ∥ → A
dec-untrunc (yes p) _ = p
dec-untrunc (no ¬p) p = absurd (∥rec∥ (λ ()) ¬p p)

inj-discrete : (A ↣ B) → Discrete B → Discrete A
inj-discrete (f , inj) eq? x y =
  map-dec inj (λ fx≢fy x≡y → fx≢fy (cong f x≡y) ) (eq? (f x) (f y))
