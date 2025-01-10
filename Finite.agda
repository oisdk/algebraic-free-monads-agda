{-# OPTIONS --safe #-}

module Finite where

open import Prelude
open import Function.Properties
open import Data.List.Membership

ℰ : Type a → Type a
ℰ A = ∃ n × ∥ Fin n ≃ A ∥


open import Data.Nat.Properties using (isSetNat)
open import Data.Fin.Injective
open import Isomorphism.Properties

isPropℰ : isProp (ℰ A)
isPropℰ (n , xe) (m , ye) = Σ≡Prop (λ _ → squash) (∥rec2∥ (isSetNat _ _) (λ lhs rhs → Fin-inj (ua (lhs ⟨ ≃-trans ⟩ ≃-sym rhs))) xe ye)

trav : ∀ {n} {P : Lift {ℓ₂ = b} (Fin n) → Type p} → (∀ x → ∥ P x ∥) → ∥ (∀ x → P x) ∥
trav {n = zero } f = ∣ (λ ()) ∣
trav {b = b} {n = suc n} f =
  let h = f (lift zero)
  in ∥liftA2∥ (λ { x xs (lift zero) → x ; x xs (lift (suc i)) → xs (lift i) }) h (trav {b = b} (f ∘′ lift ∘′ suc ∘′ lower))

travℰ : ℰ A → ((x : A) → ∥ P x ∥) → ∥ ((x : A) → P x) ∥
travℰ (n , p) k = ∥rec∥ squash (λ e → let h = ua (≃-trans (isoToEquiv ⇔-lift) e) in subst (λ t → ∀ {P : t → Type _} → ((x : t) → ∥ P x ∥) → ∥ (∀ x → P x) ∥ ) h trav k) p

module _ where
  open import Finite.OnLists

  ≃⇒ℰ! : ∃ n × (Fin n ≃ A) → ℰ! A
  ≃⇒ℰ! (n , p) .fst = tabulate (p .fst)
  ≃⇒ℰ! (n , p) .snd x =
    let e = p .snd .equiv-proof x
        h = tabulate-∈ (p .fst) (e .fst .fst)
    in subst (_∈ tabulate (p .fst)) (e .fst .snd) h

  module _ {A : Type a} where
    ℰΣ : ℰ A → ((x : A) → ℰ (P x)) → ℰ (Σ A P)
    ℰΣ (n , xs) k = ∥rec2∥ isPropℰ conv xs (travℰ (n , xs) (snd ∘′ k))
      where
      conv : Fin n ≃ A → ((x : A) → Fin (k x .fst) ≃ P x) → ℰ (Σ A P)
      conv e k′ =
        let h = ≃⇒ℰ! (_ , e) |Σ| λ x → ≃⇒ℰ! (_  , k′ x) 
        in map₂ ∣_∣ (ℬ→ℱ (ℰ!⇒ℬ h))

open import Data.Nat.Order

⇔→ℰ : A ⇔ B → ℰ A → ℰ B
⇔→ℰ i = map₂ (∥map∥ (flip ≃-trans (isoToEquiv i)))


Equiv⇒SplitSurj : (f : A → B) → isEquiv f → SplitSurjective f
Equiv⇒SplitSurj f x y = x .equiv-proof y .fst

≃⇒↠! : A ≃ B → A ↠! B
≃⇒↠! = map₂ (Equiv⇒SplitSurj _)

ℰ⇒Discrete : ℰ A → Discrete A
ℰ⇒Discrete = ∥rec∥ isPropDiscrete (flip Discrete-↠! discreteFin ∘ ≃⇒↠!) ∘′ snd


open import Data.Fin.Properties using (isPropFin1; Fin⊥)

ℰ⇒Dec : ℰ A → Dec ∥ A ∥
ℰ⇒Dec (zero  , xs) = no (∥rec2∥ (λ ()) (λ e x → Fin⊥ .fun (e .snd .equiv-proof x .fst .fst))  xs)
ℰ⇒Dec (suc n , xs) = yes (∥map∥ ((_$ zero) ∘ fst) xs)

open import Cubical.Foundations.Prelude using (isContr→isProp)

isContr⇒ℰ : isContr A → ℰ A
isContr⇒ℰ (x , p) .fst = 1
isContr⇒ℰ (x , p) .snd =
            ∣ (λ where .fst _ → x
                       .snd .equiv-proof y .fst .fst → 0
                       .snd .equiv-proof y .fst .snd → p y
                       .snd .equiv-proof y .snd (zero , q) i → zero , isProp→isSet (isContr→isProp (x , p)) x y (p y) q i) ∣

¬⇒ℰ : ¬ A → ℰ A
¬⇒ℰ ¬A .fst = 0
¬⇒ℰ ¬A .snd =
 ∣ (λ where .fst ()
            .snd .equiv-proof y → absurd (¬A y) ) ∣

ℰ× : ℰ A → ℰ B → ℰ (A × B)
ℰ× x y = ℰΣ x (const y)

ℰ⟨⊤⟩ : ℰ ⊤
ℰ⟨⊤⟩ = isContr⇒ℰ (tt , λ _ → refl)

open import Data.Nat.Properties

private variable n m : ℕ

ℰ⟨Fin⟩ : ℰ (Fin n)
ℰ⟨Fin⟩ {n = n} = n , ∣ isoToEquiv  id-⇔ ∣

ℰ⟨ℕ≤⟩ : ℰ (∃ m × m ≤ n)
ℰ⟨ℕ≤⟩ = suc _ , ∣ isoToEquiv lemma ∣
  where
  fin→≤ : Fin (suc n) → ∃ m × m ≤ n 
  fin→≤ zero    = zero , tt
  fin→≤ {n = suc n} (suc f) = let g , p = fin→≤ {n = n} f in suc g , p

  ≤→fin : ∃ m × m ≤ n → Fin (suc n)
  ≤→fin (zero , p) = zero
  ≤→fin {n = suc n} (suc m , p) = suc (≤→fin {n} (m , p))

  linv : (x : Fin (suc n)) → ≤→fin (fin→≤ x) ≡ x
  linv zero = refl
  linv {n = suc n} (suc x) = cong suc (linv {n} x)

  rinv : (x : ∃ m × m ≤ n) → fin→≤ (≤→fin x) ≡ x
  rinv {n} (zero , p) = refl
  rinv {suc n} (suc m , p) = cong (map-Σ suc id) (rinv {n} (m , p))

  lemma : Fin (suc n) ⇔ (∃ m × m ≤ n)
  lemma .fun = fin→≤
  lemma .inv = ≤→fin
  lemma .rightInv = rinv
  lemma .leftInv = linv

DecProp⇒ℰ : isProp A → Dec A → ℰ A
DecProp⇒ℰ isPropA (yes p) = isContr⇒ℰ (p , isPropA p)
DecProp⇒ℰ isPropA (no ¬p) = ¬⇒ℰ ¬p

Discrete⇒ℰ : Discrete A → {x y : A} → ℰ (x ≡ y)
Discrete⇒ℰ d = DecProp⇒ℰ (Discrete→isSet d _ _) (d _ _)

ℰ? : (∀ x → isProp (P x)) → ℰ A → ((x : A) → Dec (P x)) → ℰ (Σ A P)
ℰ? pIsProp ℰA ℰP? = ℰΣ ℰA λ x → DecProp⇒ℰ (pIsProp x) (ℰP? x)


module _ (ℰ⟨A⟩ : ℰ A) where
  ℰ⟨List·length⟩ : ∀ n → ℰ (Σ[ xs ⦂ List A ] × length xs ≡ n)
  ℰ⟨List·length⟩ zero    = ⇔→ℰ lemma ℰ⟨⊤⟩
    where
    lemma : ⊤ ⇔ (Σ[ xs ⦂ List A ] × length xs ≡ 0)
    lemma .fun _ = [] , refl
    lemma .inv _ = tt
    lemma .rightInv ([] , p) = Σ≡Prop (λ _ → isSetNat _ _) refl
    lemma .rightInv (x ∷ xs , p) = absurd (suc≢zero p)
    lemma .leftInv  _ = refl
  ℰ⟨List·length⟩ (suc n) = ⇔→ℰ lemma (ℰ× ℰ⟨A⟩ (ℰ⟨List·length⟩ n))
    where
    lemma : (A × Σ[ xs ⦂ List A ] × length xs ≡ n) ⇔ (Σ[ xs ⦂ List A ] × length xs ≡ suc n)
    lemma .fun (x , xs , p) = x ∷ xs , cong suc p
    lemma .inv ([] , p) = absurd (zero≢suc p)
    lemma .inv (x ∷ xs , p) = x , xs , suc-inj p
    lemma .rightInv ([] , p) = absurd (zero≢suc p)
    lemma .rightInv (x ∷ xs , p) = Σ≡Prop (λ _ → isSetNat _ _) refl
    lemma .leftInv (x , xs , p) = refl

  open import Isomorphism.Properties

  ℰ⟨List≤length⟩ : ∀ n → ℰ (Σ[ xs ⦂ List A ] × length xs ≤ n)
  ℰ⟨List≤length⟩ n = ⇔→ℰ lemma (ℰΣ (ℰ⟨ℕ≤⟩ {n}) (ℰ⟨List·length⟩ ∘′ fst))
    where
    lemma : (Σ[ p ⦂ (∃ m × m ≤ n) ] × Σ[ xs ⦂ List A ] × length xs ≡ fst p)
          ⇔ (Σ[ xs ⦂ List A ] × length xs ≤ n)
    lemma .fun ((m , p) , xs , q) = xs , subst (_≤ _) (sym q) p
    lemma .inv (xs , q) = (length xs , q) , xs , refl
    lemma .rightInv (xs , q) = Σ≡Prop (λ x → isProp≤ {length x}  ) refl
    lemma .leftInv  ((m , p) , xs , q) = ΣPathP (Σ≡Prop (λ x → isProp≤ {x}) q , toPathP (Σ≡Prop (λ x → isSetNat _ _) (transportRefl xs)))

  ℰ×NoDup⇒List≤ : (xs : List A) → NoDup xs → length xs ≤ ℰ⟨A⟩ .fst
  ℰ×NoDup⇒List≤ xs nd =
    let h = ((xs !!_) , NoDup⇒Inj xs nd) ⦂ (Fin (length xs) ↣ A)
    in ∥rec∥ (isProp≤ {length xs}) (λ p → ↣⇒≤ (↣-trans h (_ , ⇔-fun-inj (sym-⇔ (equivToIso p)) _ _))) (ℰ⟨A⟩ .snd)

  ℰ⟨List⟩  : ℰ (Σ[ xs ⦂ List A ] × NoDup xs)
  ℰ⟨List⟩ = ⇔→ℰ (Σ-assoc ⟨ trans-⇔ ⟩  cong-Σ lemma) (ℰ? (λ _ → isPropNoDup _) (ℰ⟨List≤length⟩ (ℰ⟨A⟩ .fst)) (NoDups? (ℰ⇒Discrete ℰ⟨A⟩) ∘′ fst))
    where
    lemma : (xs : List A) → ((length xs ≤ ℰ⟨A⟩ .fst) × NoDup xs) ⇔ NoDup xs
    lemma xs .fun = snd
    lemma xs .inv nd = ℰ×NoDup⇒List≤ xs nd , nd
    lemma xs .rightInv _ = refl
    lemma xs .leftInv x = ΣPathP (isProp≤ {length xs} _ _  , refl)

module _ {P : A → Type p} where
  ℰ⇒search :
    ℰ A → (P? : ∀ (x : A) → Dec (P x)) → Dec ∥ ∃ x × P x ∥
  ℰ⇒search ℰA P? = ∥rec∥ (isPropDec squash) (dec-trunc ∘ search) (ℰA .snd)
    where
    search′ : (f : Fin n → A) → Dec (∃ i × P (f i))
    search′ {n = zero}  f = no λ ()
    search′ {n = suc n} f with P? (f 0) | search′ (f ∘ suc)
    ... | yes p | _ = yes (0 , p)
    ... | no ¬p | yes (i , p) = yes (suc i , p)
    ... | no ¬p | no ¬ps = no λ { (zero , p) → ¬p p ; (suc i , p) → ¬ps (i , p) }

    open import Cubical.Foundations.Everything using (equivToIso)

    search : (Fin n ≃ A) → Dec (∃ x × P x)
    search f≃A = let f⇔A = equivToIso f≃A in
      iff-dec
        (map-Σ (f⇔A .fun) id ,
         map-Σ (f⇔A .inv) (subst P (sym (f⇔A .rightInv _)))) (search′ (f⇔A .fun))
