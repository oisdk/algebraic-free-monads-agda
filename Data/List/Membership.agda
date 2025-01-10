{-# OPTIONS --safe #-}

module Data.List.Membership where

open import Prelude

infixr 5 _∈_ _∈!_
_∈_ : A → List A → Type _
x ∈ xs = Fibre (xs !!_ ) x

_∈!_ : A → List A → Type _
x ∈! xs = isContr (x ∈ xs)

infixr 5 _∉_
_∉_ : A → List A → Type _
x ∉ xs = ¬ (x ∈ xs)

private variable n : ℕ

tabulate-∈ : (f : Fin n → A) (x : Fin n) → f x ∈ tabulate f
tabulate-∈ {n = suc n} f zero    = zero , refl
tabulate-∈ {n = suc n} f (suc x) =
  let i , p = tabulate-∈ (f ∘ suc) x
  in suc i , p

allFins : List (Fin n)
allFins = tabulate id

∈-allFins : (i : Fin n) → i ∈ allFins
∈-allFins = tabulate-∈ id

NoDup : {A : Type a} → List A → Type a
NoDup [] = Poly-⊤
NoDup (x ∷ xs) = (x ∉ xs) × NoDup xs

module _ (_≟_ : Discrete A) where
  module _ (x : A) where
    find : ∀ xs → Dec (x ∈ xs)
    find [] = no λ ()
    find (y ∷ xs) with x ≟ y | find xs
    ... | yes x≡y | _ = yes (zero , sym x≡y)
    ... | no _    | yes (i , x∈xs) = yes (suc i , x∈xs)
    ... | no x≢y  | no x∉xs = no λ { (zero , x∈xs) → x≢y (sym x∈xs) ; (suc i , x∈xs) → x∉xs (i , x∈xs) }

  NoDups? : (xs : List A) → Dec (NoDup xs)
  NoDups? [] = yes Poly-tt
  NoDups? (x ∷ xs) with find x xs | NoDups? xs
  NoDups? (x ∷ xs) | yes x∈xs | _ = no ((_$ x∈xs) ∘ fst)
  NoDups? (x ∷ xs) | no x∉xs | yes nds = yes (x∉xs , nds)
  NoDups? (x ∷ xs) | no x∉xs | no ¬nds = no (¬nds ∘ snd)

isPropNoDup : (xs : List A) → isProp (NoDup xs)
isPropNoDup [] _ _ = refl
isPropNoDup (x ∷ xs) (l , ls) (r , rs) = cong₂ _,_ (isProp¬ l r) (isPropNoDup xs ls rs)

NoDup⇒Inj : (xs : List A) → NoDup xs → Injective (xs !!_)
NoDup⇒Inj (x ∷ xs) nd {zero} {zero} p = refl
NoDup⇒Inj (x ∷ xs) (_ , nd) {suc i} {suc j} p = cong suc (NoDup⇒Inj xs nd p)
NoDup⇒Inj (x ∷ xs) (n , _) {zero} {suc j} p = absurd (n (j , sym p))
NoDup⇒Inj (x ∷ xs) (n , _) {suc i} {zero} p = absurd (n (i , p))

module _ {x : A} where
  infixr 5 _++◇_ _◇++_
  _++◇_ : ∀ {xs} ys → x ∈ xs → x ∈ (ys ++ xs)
  [] ++◇ p = p
  (x ∷ ys) ++◇ p = map-Σ suc id (ys ++◇ p)

  _◇++_ : ∀ xs {ys} → x ∈ xs → x ∈ (xs ++ ys)
  (x ∷ xs) ◇++ (zero , p) = zero , p
  (x ∷ xs) ◇++ (suc i , p) = map-Σ suc id (xs ◇++ (i , p))

cong-∈ : (f : A → B) (xs : List A) {x : A} → x ∈ xs → f x ∈ mapl f xs
cong-∈ f (x ∷ xs) (zero , p) = zero , cong f p
cong-∈ f (x ∷ xs) (suc i , p) = map-Σ suc id (cong-∈ f xs (i , p))

here! : ∀ {x y : A} {xs} → isContr (x ≡ y) → y ∉ xs → y ∈! x ∷ xs
here! Px p∉xs .fst = zero , Px .fst
here! Px p∉xs .snd (zero  , p∈xs) = ΣPathP (refl , Px .snd _)
here! Px p∉xs .snd (suc n , p∈xs) = absurd (p∉xs (n , p∈xs))
open import Data.Fin.Properties using (suc-injective)

module MembershipManips where
  pull : ∀ {x y : A} {xs} → x ≢ y → y ∈ x ∷ xs → y ∈ xs
  pull x≢y (zero  , y∈xxs) = absurd (x≢y y∈xxs)
  pull x≢y (suc n , y∈xxs) = n , y∈xxs
  
  push : ∀ {x y : A} {xs} → y ∈ xs → y ∈ x ∷ xs
  push (n , p) = suc n , p
  
  pull! : ∀ {x y : A} {xs} → x ≢ y → y ∈! x ∷ xs → y ∈! xs
  pull! x≢y ((zero  , y∈xxs) , c) = absurd (x≢y y∈xxs)
  pull! x≢y ((suc n , y∈xxs) , c) .fst = (n , y∈xxs)
  pull! x≢y ((suc n , y∈xxs) , c) .snd (m , q) i = pull x≢y (c (suc m , q) i)
  
  push! : ∀ {x y : A} {xs} → x ≢ y → y ∈! xs → y ∈! x ∷ xs
  push! ¬Px x∈!xs .fst = push (x∈!xs .fst)
  push! ¬Px x∈!xs .snd (zero   , px) = absurd (¬Px px)
  push! ¬Px x∈!xs .snd (suc n  , y∈xs) i = push (x∈!xs .snd (n , y∈xs) i)

open MembershipManips

module _ {a} {A : Type a} (_≟_ : Discrete A) where
  isSet⟨A⟩ : isSet A
  isSet⟨A⟩ = Discrete→isSet _≟_

  infixl 6 _\\_
  _\\_ : List A → A → List A
  xs \\ x = foldr f [] xs
    where
    f : A → List A → List A
    f y xs with x ≟ y
    ... | yes p = xs
    ... | no  p = y ∷ xs

  uniques : List A → List A
  uniques = foldr f []
    where
    f : A → List A → List A
    f x xs = x ∷ (xs \\ x)

  x∉xs\\x : ∀ x xs → x ∉ xs \\ x
  x∉xs\\x x (y ∷ xs) (n , x∈xs) with x ≟ y
  x∉xs\\x x (y ∷ xs) (n      , x∈xs)  | yes p = x∉xs\\x x xs (n , x∈xs)
  x∉xs\\x x (y ∷ xs) (zero   , y≡x)   | no ¬p = ¬p (sym y≡x)
  x∉xs\\x x (y ∷ xs) (suc n  , x∈xs)  | no ¬p = x∉xs\\x x xs (n , x∈xs)

  x∈!x∷xs\\x : ∀ x xs → x ∈! x ∷ xs \\ x
  x∈!x∷xs\\x x xs = here! (refl ,  isSet⟨A⟩ _ _ _) (x∉xs\\x x xs)

  x∉xs⇒x∉xs\\y : ∀ (x : A) y xs → x ∉ xs → x ∉ xs \\ y
  x∉xs⇒x∉xs\\y x y (z ∷ xs) x∉xs x∈xs\\y with y ≟ z
  x∉xs⇒x∉xs\\y x y (z ∷ xs) x∉xs x∈xs\\y | yes p =
    x∉xs⇒x∉xs\\y x y xs (x∉xs ∘ map-Σ suc id) x∈xs\\y
  x∉xs⇒x∉xs\\y x y (z ∷ xs) x∉xs (zero  , x∈xs\\y) | no ¬p =
    x∉xs (zero , x∈xs\\y)
  x∉xs⇒x∉xs\\y x y (z ∷ xs) x∉xs (suc n , x∈xs\\y) | no ¬p =
    x∉xs⇒x∉xs\\y x y xs (x∉xs ∘ map-Σ suc id) (n , x∈xs\\y)

  open import Data.Fin.Properties using (zero≢suc ; suc≢zero)

  x∈!xs⇒x∈!xs\\y : ∀ (x : A) y xs → y ≢ x → x ∈! xs → x ∈! xs \\ y
  x∈!xs⇒x∈!xs\\y x y (z ∷ xs) y≢x x∈!xs with y ≟ z
  x∈!xs⇒x∈!xs\\y x y (z ∷ xs) y≢x x∈!xs | yes p =
    x∈!xs⇒x∈!xs\\y x y xs y≢x (pull! (y≢x ∘′ (p ⨾_)) x∈!xs)
  x∈!xs⇒x∈!xs\\y x y (z ∷ xs) y≢x ((zero  , x∈xs) , uniq) | no ¬p =
    here! (x∈xs , isSet⟨A⟩ _ _ _) (x∉xs⇒x∉xs\\y x y xs (zero≢suc ∘′ cong fst ∘′ uniq ∘′ push))
  x∈!xs⇒x∈!xs\\y x y (z ∷ xs) y≢x ((suc n , x∈xs) , uniq) | no ¬p =
    push! z≢x (x∈!xs⇒x∈!xs\\y x y xs y≢x (pull! z≢x ((suc n , x∈xs) , uniq)))
    where z≢x = suc≢zero ∘ cong fst ∘′ uniq ∘′ (zero ,_)

  ∈⇒∈! : (x : A) (xs : List A) → x ∈ xs → x ∈! uniques xs
  ∈⇒∈! x (y ∷ xs) (zero  , x∈xs) =
    subst (_∈! (y ∷ uniques xs \\ y)) x∈xs (x∈!x∷xs\\x y (uniques xs))
  ∈⇒∈! x (y ∷ xs) (suc n , x∈xs) with y ≟ x
  ... | yes p = subst (_∈! (y ∷ uniques xs \\ y)) p (x∈!x∷xs\\x y (uniques xs))
  ... | no ¬p = push! ¬p (x∈!xs⇒x∈!xs\\y x y (uniques xs) ¬p (∈⇒∈! x xs (n , x∈xs)))
