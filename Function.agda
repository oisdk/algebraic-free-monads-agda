{-# OPTIONS --safe #-}

module Function where

open import Level

infixr 9 _∘′_
_∘′_ : ∀ {A : Type a} {B : A → Type b} {C : {x : A} → B x → Type c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘′ g = λ x → f (g x)
{-# INLINE _∘′_ #-}

infixr 9 _∘_
_∘_ : (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

flip : ∀ {A : Type a} {B : Type b} {C : A → B → Type c} →
        ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y
{-# INLINE flip #-}

id : ∀ {A : Type a} → A → A
id x = x
{-# INLINE id #-}

const : A → B → A
const x _ = x
{-# INLINE const #-}

infixr -1 _$_
_$_ : ∀ {A : Type a} {B : A → Type b}
      → (∀ (x : A) → B x)
      → (x : A)
      → B x
f $ x = f x
{-# INLINE _$_ #-}

infixl 0 _|>_
_|>_ : ∀ {A : Type a} {B : A → Type b}
      → (x : A)
      → (∀ (x : A) → B x)
      → B x
_|>_ = flip _$_
{-# INLINE _|>_ #-}

infixl 1 _⟨_⟩_
_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y
{-# INLINE _⟨_⟩_ #-}

infixl 0 the
the : (A : Type a) → A → A
the _ x = x
{-# INLINE the #-}

syntax the A x = x ⦂ A

Dom : {A : Type a} → (A → B) → Type a
Dom {A = A} _ = A

infix 0 case_of_
case_of_ : A → (A → B) → B
case x of f = f x
{-# INLINE case_of_ #-}

infixr -1 _⇒_
_⇒_ : (A → Type b) → (A → Type c) → Type _
F ⇒ G = ∀ {x} → F x → G x

infixr -1 _↣_ _↠_ _↠!_
infixl -1 _↢_ _↞_ _!↞_

open import Path

Injective : (f : A → B) → Type _
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

open import Data.Sigma

_↣_ : Type a → Type b → Type _
A ↣ B = Σ[ f ⦂ (A → B) ] × Injective f

_↢_ : Type a → Type b → Type _
_↢_ = flip _↣_

↣-refl : A ↣ A
↣-refl .fst = id
↣-refl .snd = id

↣-trans : A ↣ B → B ↣ C → A ↣ C
↣-trans (f , fi) (g , gi) .fst = g ∘ f
↣-trans (f , fi) (g , gi) .snd = fi ∘ gi

private module RecordFibre where
  record Fibre {A : Type a} {B : Type b} (f : A → B) (y : B) : Type (a ℓ⊔ b)
  record Fibre f y where
    no-eta-equality; constructor _,↠_
    field  preimage  : Dom f
           reflects  : f preimage ≡ y

open import Isomorphism

Fibre : (A → B) → B → Type _
Fibre f y = ∃ x × f x ≡ y

-- Surjected⇔Σ : (f : A → B) (y : B) → Fibre f y ⇔ fibre f y
-- Surjected⇔Σ f y .fun s = preimage s , reflects s
-- Surjected⇔Σ f y .inv s .preimage = fst s
-- Surjected⇔Σ f y .inv s .reflects = snd s
-- Surjected⇔Σ f y .rightInv s = refl
-- Surjected⇔Σ f y .leftInv s i .preimage = preimage s
-- Surjected⇔Σ f y .leftInv s i .reflects = reflects s

-- open import HLevels
-- open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

-- Surj≡Prop : (f : A → B) (y : B) → isSet B → {lhs rhs : Fibre f y} → (preimage lhs ≡ preimage rhs) → lhs ≡ rhs
-- Surj≡Prop f y s {lhs = lhs} {rhs = rhs} p =
--   sym (Surjected⇔Σ f y .leftInv _) ⨾
--   cong (Surjected⇔Σ f y .inv) (Σ≡Prop (λ _ → s _ _) p) ⨾
--   Surjected⇔Σ f y .leftInv _

SplitSurjective : (f : A → B) → Type _
SplitSurjective f = ∀ y → Fibre f y

_↠!_ : Type a → Type b → Type _
A ↠! B = Σ[ f ⦂ (A → B) ] × SplitSurjective f

_!↞_ : Type a → Type b → Type _
_!↞_ = flip _↠!_

surj-inv : (A ↠! B) → (B → A)
surj-inv s x = s .snd x .fst

open import Cubical.HITs.PropositionalTruncation renaming (∥_∥₁ to ∥_∥)

Surjective : (f : A → B) → Type _
Surjective f = ∀ y → ∥ Fibre f y ∥

Iso : (A → B) → Type _
Iso {A = A} {B = B} f = Σ[ g ⦂ (B → A) ] × (f ∘ g ≡ id) × (g ∘ f ≡ id)

_↠_ : Type a → Type b → Type _
A ↠ B = Σ[ f ⦂ (A → B) ] × Surjective f

_↞_ : Type a → Type b → Type _
_↞_ = flip _↠_

↠!-trans : (A ↠! B) → (B ↠! C) → A ↠! C
↠!-trans f g .fst = g .fst ∘ f .fst 
↠!-trans f g .snd y .fst = f .snd (g .snd y .fst) .fst
↠!-trans f g .snd y .snd = cong (g .fst) (f .snd (g .snd y .fst) .snd) ⨾ g .snd y .snd

↠!-refl : A ↠! A
↠!-refl .fst = id
↠!-refl .snd x .fst = x
↠!-refl .snd x .snd = refl

↠!⇒↢ : A ↠! B → A ↢ B
↠!⇒↢ f .fst y = f .snd y .fst
↠!⇒↢ f .snd p = sym (f .snd _ .snd) ⨾ cong (f .fst) p ⨾ f .snd _ .snd

infix 4 _↔_
_↔_ : Type a → Type b → Type _
A ↔ B = (A → B) × (B → A)

↔-refl : A ↔ A
↔-refl = id , id

↔-sym : A ↔ B → B ↔ A
↔-sym (x , y) = (y , x)

↔-trans : A ↔ B → B ↔ C → A ↔ C
↔-trans (f , f⁻) (g , g⁻) .fst = g ∘ f
↔-trans (f , f⁻) (g , g⁻) .snd = f⁻ ∘ g⁻

iso⇒iff : A ⇔ B → A ↔ B
iso⇒iff f = f .fun , f .inv
