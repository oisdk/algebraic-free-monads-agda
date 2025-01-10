{-# OPTIONS --safe #-}

module Truth.Logic where

open import Prelude
open import Truth.Definition
open import Truth.Combinators

open import Cubical.HITs.PropositionalTruncation

interleaved mutual
  infixl 7 _|∧|_
  infixl 6 _|∨|_
  infixr 5 _|→|_
  _|∧|_ _|∨|_ _|→|_ : Ω a → Ω b → Ω _

  ProofOf (X |∧| Y) = ProofOf X × ProofOf Y
  ProofOf (X |→| Y) = ProofOf X → ProofOf Y
  ProofOf (X |∨| Y) = ∥ ProofOf X ⊎ ProofOf Y ∥
  IsProp (_  |→| Y) = isProp→ (IsProp Y)
  IsProp (x |∧| y) = isProp× (x .IsProp) (y .IsProp)
  IsProp (x |∨| y) = squash

|∀| : (A → Ω b) → Ω _
ProofOf (|∀| f) = ∀ x → ProofOf (f x)
IsProp  (|∀| f) = isPropΠ λ x → IsProp (f x)

|∃| : (A → Ω b) → Ω _
ProofOf (|∃| f) = ∥ ∃ x × ProofOf (f x) ∥
IsProp  (|∃| f) = squash

_|↔|_ : Ω a → Ω b → Ω _
X |↔| Y = (X |→| Y) |∧| (Y |→| X)

|→|-id : (x : Ω a) → x |→| x ≡ True
|→|-id x = proves id

Not : Ω a → Ω a
Not x .ProofOf = ¬ x .ProofOf
Not x .IsProp = isProp→ λ ()

|→|-idˡ : (x : Ω a) → True |→| x ≡ x
|→|-idˡ {a = a} x = (_$ (Poly-tt {ℓ = a})) iff const

|→|-annʳ : (x : Ω a) → x |→| True {ℓ = b} ≡ True
|→|-annʳ x = const Poly-tt iff (λ _ _ → Poly-tt)

|→|-annˡ : (x : Ω a) → False {ℓ = b} |→| x ≡ True
|→|-annˡ x = (λ _ → Poly-tt) iff λ _ ()

Ω∣_∣ : Type a → Ω a
ProofOf  Ω∣ P ∣ = ∥ P ∥
IsProp   Ω∣ P ∣ = squash

infix 5.5 _|≡|_
_|≡|_ : A → A → Ω _
x |≡| y = Ω∣ x ≡ y ∣

|T| : Bool → Ω a
|T| = bool′ False True

|→|-trans : (x y z : Ω a) → ((x |→| y) |∧| (y |→| z)) |→| (x |→| z) ≡ True
|→|-trans x y z = const Poly-tt iff const (uncurry (flip _∘_))

|→|-curry : (X Y Z : Ω a) → (X |∧| Y |→| Z) ≡ (X |→| Y |→| Z)
|→|-curry _ _ _ = curry iff uncurry

|→|-|∧| : (x y z : Ω a) → (x |→| (y |∧| z)) ≡ (x |→| y) |∧| (x |→| z)
|→|-|∧| _ _ _ = (λ f → fst ∘ f , snd ∘ f) iff λ { (f , g) x → f x , g x }

|∨|-|→| : (x y z : Ω a) → ((x |∨| y) |→| z) ≡ (x |→| z) |∧| (y |→| z)
|∨|-|→| _ _ z =
    (λ f → f ∘ ∣_∣ ∘ inl , f ∘ ∣_∣ ∘ inr) iff
    λ { (f , g) → rec (z .IsProp) (either f g) }

∧-com : (x y : Ω a) → x |∧| y ≡ y |∧| x
∧-com _ _ = (λ { (x , y) → (y , x) }) iff λ { (x , y) → y , x }

∧-idem : (x : Ω a) → x |∧| x ≡ x
∧-idem _ = fst iff (λ x → x , x)

∨-idem : (x : Ω a) → x |∨| x ≡ x
∨-idem x = (rec (x .IsProp) (either id id)) iff (∣_∣ ∘ inl)

∨-com : (x y : Ω a) → x |∨| y ≡ y |∨| x
∨-com x y = (rec squash (∣_∣ ∘ either inr inl)) iff (rec squash (∣_∣ ∘ either inr inl))

∧-ann : (x : Ω a) → x |∧| (False {a}) ≡ False
∧-ann x = snd iff λ ()

refute : (x : Ω a) → ¬ ProofOf x → x ≡ False
refute x ¬p = (absurd ∘ ¬p) iff λ ()

∨-assoc : (x y z : Ω a) → (x |∨| y) |∨| z ≡ x |∨| (y |∨| z)
∨-assoc x y z =
    (rec squash (either (rec squash  (∣_∣ ∘ mapʳ (∣_∣ ∘ inl))) (∣_∣ ∘ inr ∘ ∣_∣ ∘ inr ))) iff
    (rec squash (either (∣_∣ ∘ inl ∘ ∣_∣ ∘ inl) (rec squash (∣_∣ ∘ mapˡ (∣_∣ ∘ inr) ))))

∧-assoc : (x y z : Ω a) → (x |∧| y) |∧| z ≡ x |∧| (y |∧| z)
∧-assoc x y z =
    (λ { ((x , y) , z) → x , y , z }) iff
    λ { (x , y , z) → (x , y)  , z }

∧-id : (x : Ω a) → (True {a}) |∧| x ≡ x
∧-id x = snd iff (Poly-tt ,_)

∨-ann : (x : Ω a) → x |∨| (True {a}) ≡ True
∨-ann x = (const Poly-tt) iff (∣_∣ ∘ inr)

∨-id : (x : Ω a) → x |∨| (False {a}) ≡ x
∨-id x = (rec (x .IsProp) (either id (λ ()))) iff (∣_∣ ∘ inl)

∨-idˡ : (x : Ω a) → (False {a}) |∨| x ≡ x
∨-idˡ x = (rec (x .IsProp) (either (λ ()) id)) iff (∣_∣ ∘ inr)

∧-distrib-∨ : (x y z : Ω a) → x |∧| (y |∨| z) ≡ (x |∧| y) |∨| (x |∧| z)
∧-distrib-∨ x y z =
    (uncurry (λ xp → rec squash (∣_∣ ∘ map-⊎ (xp ,_) (xp ,_)) )) iff
    (rec (isProp× (x .IsProp) squash) (either (map₂ (∣_∣ ∘ inl)) (map₂ (∣_∣ ∘ inr))))

∨-distrib-∧ : (x y z : Ω a) → x |∨| (y |∧| z) ≡ (x |∨| y) |∧| (x |∨| z)
∨-distrib-∧ x y z =
    (rec (isProp× squash squash) (either (λ x → ∣ inl x ∣ , ∣ inl x ∣) λ { (yp , zp) → ∣ inr yp ∣ , ∣ inr zp ∣ })) iff
    (uncurry (rec2 squash  λ { (inl x) _ → ∣ inl x ∣ ; _ (inl x) → ∣ inl x ∣ ; (inr y) (inr z) → ∣ inr (y , z) ∣  }))
