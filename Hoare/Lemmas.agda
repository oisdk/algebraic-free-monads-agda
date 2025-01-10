{-# OPTIONS --safe --lossy-unification #-}

open import Prelude
open import Signatures
open import FinitenessConditions
open import FreeMonad.PackagedTheory

module Hoare.Lemmas {ℓ} (𝒯 : FullTheory ℓ) where

open import FreeMonad.Quotiented 𝒯

open import Hoare.Definition 𝒯
open import Truth

sef-dsef-cont : ∀ {B : Type b} → (ps : Σ[ p ⦂ Term A ] × SEF b p × DET b p) → (k : A → A → Term B) → (do x ← ps .fst ; y ← ps .fst ; k x y) ≡ (do x ← ps .fst ; k x x)
sef-dsef-cont (p , s , d) k = d k ⨾ x ⇐ p ⨾/ s (k x x)

module _ {A : Type a} where
  dsef-alt : (p : Term A)
           → DET (ℓsuc a) p
           → (do x ← p ; y ← p ; return (x |≡| y)) ≡ (do p ; p ; return True)
  dsef-alt p d = d (λ x y → return (x |≡| y)) ⨾ x ⇐ p ⨾/ _ ⇐ p ⨾/ cong return (proves ∣ refl ∣)

module _ {B : Type b} where
  sef-com : (p : Term A) (xs : Term B) → SEF b p →
    (do x ← xs ; p ; return x) ≡ (do p ; xs)
  sef-com p xs sef⟨p⟩ =
    (do x ← xs
        p
        return x) ≡⟨ x ⇐ xs ⨾/ sef⟨p⟩ (return x) ⟩

    (do x ← xs
        return x) ≡⟨ >>=-idʳ _ ⟩

    xs ≡˘⟨ sef⟨p⟩ xs ⟩

    (do p
        xs) ∎

_⟪_⟫_ : Term A → (A → B → C) → Term B → Term C
xs ⟪ f ⟫ ys = do x ← xs ; y ← ys ; return (f x y)

infixl 6 _⟨∧⟩_
_⟨∧⟩_ : Term (Ω a) → Term (Ω a) → Term (Ω a)
xs ⟨∧⟩ ys = xs ⟪ _|∧|_ ⟫ ys

infixl 5 _⟨∨⟩_
_⟨∨⟩_ : Term (Ω a) → Term (Ω a) → Term (Ω a)
xs ⟨∨⟩ ys = xs ⟪ _|∨|_ ⟫ ys

⟪assoc⟫ : ∀ {d} {D : Type d} → (xs : Term A) (ys : Term B) (f : A → B → C) (k : C → Term D) →
          (xs ⟪ f ⟫ ys) >>= k ≡ (do x ← xs ; y ← ys ; k (f x y))
⟪assoc⟫ xs ys f k = assoc xs _ _ ⨾ x ⇐ xs ⨾/ assoc ys _ _

_⟪,⟫_ : Term A → Term B → Term (A × B)
_⟪,⟫_ = _⟪ _,_ ⟫_

assoc-⟪,⟫ : (xs : Term A) (ys : Term B) (k : A → B → Term C) → 
            (xs ⟪,⟫ ys) >>= uncurry k ≡ (do x ← xs ; y ← ys ; k x y)
assoc-⟪,⟫ xs ys k = ⟪assoc⟫ xs ys _,_ (uncurry k)

sef-<$> : (f : A → B) (p : Term A) → SEF c p → SEF c (f <$> p)
sef-<$> f p s k =
  (f <$> p) >> k ≡⟨ assoc p _ _ ⟩
  p >> k ≡⟨ s k ⟩
  k ∎

det-<$> : (f : A → B) (p : Term A) → DET c p → DET c (f <$> p)
det-<$> f p s k =
  (do x ← f <$> p; y ← f <$> p; k x y) ≡⟨ assoc p _ _ ⟩
  (do x ← p; y ← f <$> p; k (f x) y) ≡⟨ x ⇐ p ⨾/ assoc p _ _ ⟩
  (do x ← p; y ← p; k (f x) (f y)) ≡⟨ s (λ x y → k (f x) (f y)) ⟩
  (do x ← p; p; k (f x) (f x)) ≡˘⟨ x ⇐ p ⨾/ assoc p _ _ ⟩
  (do x ← p; f <$> p; k (f x) (f x)) ≡˘⟨ assoc p _ _ ⟩
  (do x ← f <$> p; f <$> p; k x x) ∎

sef-⟪,⟫ : (p : Term A) (q : Term B) →
          SEF c p → SEF c q → SEF c (p ⟪,⟫ q)
sef-⟪,⟫ p q sp sq k =
  (p ⟪,⟫ q) >> k ≡⟨ assoc-⟪,⟫ p q _ ⟩
  p >> q >> k ≡⟨ cong (p >>_) (sq k) ⟩
  p >> k ≡⟨ sp k ⟩
  k ∎

sef-com′ : (p : Term A) (q : Term B)
         → SEF c p → SEF c q
         → DET c (p ⟪,⟫ q) → {R : Type c} (k : A → B → Term R) →
           (do x ← p ; y ← q ; k x y) ≡ (do y ← q ; x ← p ; k x y)
sef-com′ p q sp sq dpq k =
  (do x ← p ; y ← q ; k x y) ≡˘⟨ assoc-⟪,⟫ p q _ ⟩
  (do xy ← p ⟪,⟫ q ; uncurry k xy) ≡˘⟨ sef-dsef-cont (p ⟪,⟫ q , sef-⟪,⟫ p q sp sq , dpq) (λ xy xy′ → k (xy′ .fst) (xy .snd)) ⟩
  (do xy ← p ⟪,⟫ q ; xy′ ← p ⟪,⟫ q ; k (xy′ .fst) (xy .snd)) ≡⟨ assoc-⟪,⟫ p q _ ⟩
  (do _ ← p ; y ← q ; xy′ ← p ⟪,⟫ q ; k (xy′ .fst) y) ≡⟨ sp _ ⟩
  (do y ← q ; xy′ ← p ⟪,⟫ q ; k (xy′ .fst) y) ≡⟨ y ⇐ q ⨾/ assoc-⟪,⟫ p q _ ⟩
  (do y ← q ; x ← p ; _ ← q ; k x y) ≡⟨ y ⇐ q ⨾/ x ⇐ p ⨾/ sq (k x y) ⟩
  (do y ← q ; x ← p ; k x y) ∎


⟨∧⟩-assoc : (x y z : Term (Ω a)) → (x ⟨∧⟩ y) ⟨∧⟩ z ≡ x ⟨∧⟩ (y ⟨∧⟩ z)
⟨∧⟩-assoc x y z =
  (x ⟨∧⟩ y) ⟨∧⟩ z ≡⟨⟩
  (do xy ← (x ⟨∧⟩ y); z′ ← z; return (xy |∧| z′)) ≡⟨ assoc x _ _  ⟩
  (do x′ ← x; xy ← (do y′ ← y; return (x′ |∧| y′)); z′ ← z; return (xy |∧| z′)) ≡⟨ x′ ⇐ x ⨾/ assoc y _ _ ⟩
  (do x′ ← x; y′ ← y; z′ ← z; return ((x′ |∧| y′) |∧| z′)) ≡⟨ x′ ⇐ x ⨾/ y′ ⇐ y ⨾/ z′ ⇐ z ⨾/ cong return ((λ { ((x , y) , z) → x , y , z }) iff λ { (x , y , z) → (x , y) , z })  ⟩
  (do x′ ← x; y′ ← y; z′ ← z; return (x′ |∧| (y′ |∧| z′))) ≡˘⟨ x′ ⇐ x ⨾/ assoc y _ _ ⨾ y′ ⇐ y ⨾/ assoc z _ _ ⟩
  (do x′ ← x; yz ← (y ⟨∧⟩ z); return (x′ |∧| yz)) ≡⟨⟩
  x ⟨∧⟩ (y ⟨∧⟩ z) ∎
