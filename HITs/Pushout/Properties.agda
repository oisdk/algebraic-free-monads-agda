{-# OPTIONS --safe #-}

open import Prelude

module HITs.Pushout.Properties
  {A : Type a} {B : Type b} {C : Type c}
  {f : A → B} {g : A → C}
  where

open import HITs.Pushout.Base f g
open import HITs.Pushout.Eliminators {f = f} {g = g}

open import Finite
open import Data.List
open import Data.List.Membership

Push : List A → B ⊎ C → B ⊎ C → Type-
Push []        x        y = x ≡ y
Push (i ∷ is)  (inl x)  y = x ≡ f i × Push is (inr (g i)) y
Push (i ∷ is)  (inr x)  y = x ≡ g i × Push is (inl (f i)) y

private module BackToExample (i j : A) (x x′ : B) where
  _ :
    Push (i ∷ j ∷ []) (inl x) (inl x′) ≡
    (x ≡ f i × g i ≡ g j × inl (f j) ≡ inl x′)
  _ = refl

_≈*_ : B ⊎ C → B ⊎ C → Type _ 
x ≈* y = ∃ p × Push p x y

refl-≈* : ∀ {x} → x ≈* x
refl-≈* = [] , refl

trans-≈* : ∀ {x y z} → x ≈* y → y ≈* z → x ≈* z
trans-≈* ([] , p) rs = subst (_≈* _) (sym p) rs
trans-≈* {x = inl x} (l ∷ ls , p , ps) rs = map-Σ (l ∷_) (p ,_) (trans-≈* (ls , ps) rs)
trans-≈* {x = inr x} (l ∷ ls , p , ps) rs = map-Σ (l ∷_) (p ,_) (trans-≈* (ls , ps) rs)

sym-≈* : ∀ {x y} → x ≈* y → y ≈* x
sym-≈* p = go p refl-≈*
  where
  go : ∀ {x y z} → x ≈* y → x ≈* z → y ≈* z
  go ([] , p) rs = subst (_≈* _) p rs
  go {x = inl x} (i ∷ is , p , ps) (js , rs) = go (is , ps) (i ∷ js , refl , subst (flip (Push js) _) (cong inl p) rs)
  go {x = inr x} (i ∷ is , p , ps) (js , rs) = go (is , ps) (i ∷ js , refl , subst (flip (Push js) _) (cong inr p) rs)

module PushoutQuot where
  Pushout′ : Type _
  Pushout′ = (B ⊎ C) / λ x y → ∥ x ≈* y ∥

  pull-struct : (x y : B ⊎ C) → x ≈* y → pull x ≡ pull y
  pull-struct x       y ([] , ps) = cong pull ps
  pull-struct (inl x) y (i ∷ is , p , ps) = cong inl p ⨾ push i ⨾ pull-struct _ y (is , ps)
  pull-struct (inr x) y (i ∷ is , p , ps) = cong inr p ⨾ sym (push i) ⨾ pull-struct _ y (is , ps)

  Pushout⇔quot : Pushout ⇔ Pushout′
  Pushout⇔quot .fun = rec squash/ ([_] ∘ inl) ([_] ∘ inr) λ i → eq/ _ _ ∣ (i ∷ []) , refl , refl ∣
  Pushout⇔quot .inv = rec/ trunc (inl ▿ inr) λ x y → ∥rec∥ (trunc _ _) (pull-struct x y)
  Pushout⇔quot .rightInv = elimProp/ (λ _ → squash/ _ _) (either (λ _ → refl) (λ _ → refl))
  Pushout⇔quot .leftInv  = elimProp _ (λ _ → trunc _ _) (λ _ → refl) λ _ → refl


  push-struct : (x y : B ⊎ C) → pull x ≡ pull y → ∥ x ≈* y ∥
  push-struct x y p =
    effective/
      (λ _ _ → squash)
      (record { reflexive = λ _ → ∣ refl-≈* ∣
              ; symmetric = λ _ _ → ∥map∥ sym-≈*
              ; transitive = λ _ _ _ → ∥liftA2∥ trans-≈* })
      x y
      (un-pull x y (cong (Pushout⇔quot .fun) p))
    where
    un-pull : (x y : B ⊎ C) → Pushout⇔quot .fun (pull x) ≡ Pushout⇔quot .fun (pull y) → [ x ] ≡ ([ y ] ⦂ Pushout′)
    un-pull (inl _) (inl _) p = p
    un-pull (inl _) (inr _) p = p
    un-pull (inr _) (inl _) p = p
    un-pull (inr _) (inr _) p = p

open PushoutQuot using (push-struct; pull-struct) public

module _
  (o : ℰ A)
  (l : Discrete B)
  (r : Discrete C) where

  discA : Discrete A
  discA = ℰ⇒Discrete o


  trunc-loopₗ : ∀ {x y} i is → i ∈ is → Push is x y → inl (f i) ≈* y
  trunc-loopₗ {x = inl x} i (j ∷ is) (zero  , i∈is) (p , ps) = j ∷ is , cong f (sym i∈is) , ps
  trunc-loopₗ {x = inr x} i (j ∷ is) (zero  , i∈is) (p , ps) = (is , subst (flip (Push is) _ ∘ inl ∘ f) i∈is ps)
  trunc-loopₗ {x = inl x} i (j ∷ is) (suc k , i∈is) (p , ps) = trunc-loopₗ i is (k , i∈is) ps
  trunc-loopₗ {x = inr x} i (j ∷ is) (suc k , i∈is) (p , ps) = trunc-loopₗ i is (k , i∈is) ps

  trunc-loopₗ-loopless : ∀ {x y} i is → (i∈is : i ∈ is) → (x~y : Push is x y) → NoDup is → NoDup (trunc-loopₗ i is i∈is x~y .fst)
  trunc-loopₗ-loopless {x = inl x} i (j ∷ is) (zero  , i∈is) x~y nd = nd
  trunc-loopₗ-loopless {x = inr x} i (j ∷ is) (zero  , i∈is) x~y nd = snd nd
  trunc-loopₗ-loopless {x = inl x} i (j ∷ is) (suc k , i∈is) (_ , x~y) (_ , nd) = trunc-loopₗ-loopless i is (k , i∈is) x~y nd
  trunc-loopₗ-loopless {x = inr x} i (j ∷ is) (suc k , i∈is) (_ , x~y) (_ , nd) = trunc-loopₗ-loopless i is (k , i∈is) x~y nd

  trunc-loopᵣ : ∀ {x y} i is → i ∈ is → Push is x y → inr (g i) ≈* y
  trunc-loopᵣ {x = inr x} i (j ∷ is) (zero  , i∈is) (p , ps) = j ∷ is , cong g (sym i∈is) , ps
  trunc-loopᵣ {x = inr x} i (j ∷ is) (suc k , i∈is) (p , ps) = trunc-loopᵣ i is (k , i∈is) ps
  trunc-loopᵣ {x = inl x} i (j ∷ is) (zero  , i∈is) (p , ps) = (is , subst (flip (Push is) _ ∘ inr ∘ g) i∈is ps)
  trunc-loopᵣ {x = inl x} i (j ∷ is) (suc k , i∈is) (p , ps) = trunc-loopᵣ i is (k , i∈is) ps

  trunc-loopᵣ-loopless : ∀ {x y} i is → (i∈is : i ∈ is) → (x~y : Push is x y) → NoDup is → NoDup (trunc-loopᵣ i is i∈is x~y .fst)
  trunc-loopᵣ-loopless {x = inr x} i (j ∷ is) (zero  , i∈is) x~y nd = nd
  trunc-loopᵣ-loopless {x = inl x} i (j ∷ is) (zero  , i∈is) x~y nd = snd nd
  trunc-loopᵣ-loopless {x = inr x} i (j ∷ is) (suc k , i∈is) (_ , x~y) (_ , nd) = trunc-loopᵣ-loopless i is (k , i∈is) x~y nd
  trunc-loopᵣ-loopless {x = inl x} i (j ∷ is) (suc k , i∈is) (_ , x~y) (_ , nd) = trunc-loopᵣ-loopless i is (k , i∈is) x~y nd

  Loopless : ∀ {x y} → x ≈* y → Type a
  Loopless = NoDup ∘ fst

  cons-l : ∀ i {x} → (p : inr (g i) ≈* x) → Loopless p → Σ (inl (f i) ≈* x) Loopless 
  cons-l i (is , pt) ls with find discA i is
  ... | no  i∉is = (i ∷ is , refl , pt) , i∉is , ls
  ... | yes i∈is = trunc-loopₗ i is i∈is pt , trunc-loopₗ-loopless i is i∈is pt ls

  cons-r : ∀ i {x} → (p : inl (f i) ≈* x) → Loopless p → Σ (inr (g i) ≈* x) Loopless
  cons-r i ([] , pt) ls = (i ∷ [] , refl , pt) , (λ ()) , Poly-tt
  cons-r i (is , pt) ls with find discA i is
  ... | no  i∉is = (i ∷ is , refl , pt) , i∉is , ls
  ... | yes i∈is = trunc-loopᵣ i is i∈is pt , trunc-loopᵣ-loopless i is i∈is pt ls

  deloop  : ∀ {x y} → x ≈* y → Σ[ p ⦂ x ≈* y ] × Loopless p
  deloop ([] , pt) = ([] , pt) , Poly-tt
  deloop {x = inl x} (i ∷ is , p , pt) = subst (λ e → Σ (inl e ≈* _) Loopless) (sym p) (uncurry (cons-l i) (deloop (is , pt)))
  deloop {x = inr x} (i ∷ is , p , pt) = subst (λ e → Σ (inr e ≈* _) Loopless) (sym p) (uncurry (cons-r i) (deloop (is , pt)))

  ℰPush : ∀ {x y} → (is : List A) → ℰ (Push is x y)
  ℰPush [] = Discrete⇒ℰ (Discrete-⊎ l r)
  ℰPush {x = inl x} (i ∷ is) = ℰ× (Discrete⇒ℰ l) (ℰPush is)
  ℰPush {x = inr x} (i ∷ is) = ℰ× (Discrete⇒ℰ r) (ℰPush is)

  module _ {x y : B ⊎ C} where
    ℰLoopless′ : ℰ (Σ[ p ⦂ List A ] × NoDup p × Push p x y)
    ℰLoopless′ =  subst ℰ (isoToPath ⇔-Σ-assoc) (ℰΣ (ℰ⟨List⟩ o) (ℰPush ∘′ fst))

    ℰLoopless : ℰ (Σ[ p ⦂ x ≈* y ] × Loopless p)
    ℰLoopless = subst ℰ (cong (Σ (List A)) (funExt λ is → isoToPath ⇔-Σ-swap) ⨾ sym (isoToPath ⇔-Σ-assoc)) ℰLoopless′

  fin-disc-pushout : Discrete Pushout
  fin-disc-pushout = elimProp2 _ (λ _ _ → isPropDec (trunc _ _)) go
    where
    go : (x y : B ⊎ C) → Dec (pull x ≡ pull y)
    go x y = iff-dec (∥rec∥ (trunc _ _) (pull-struct _ _ ∘ fst) , ∥map∥ deloop ∘ push-struct _ _) (ℰ⇒Dec (ℰLoopless {x = x} {y = y}))
