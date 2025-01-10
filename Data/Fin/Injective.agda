{-# OPTIONS --safe #-}

module Data.Fin.Injective where

open import Prelude
open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat.Properties
import Data.Nat.Order as ℕ

private variable n m : ℕ

open DiscreteFin

_≢ᶠ_ : Fin n → Fin n → Type
x ≢ᶠ y = T (! (x ≡ᴮ y))

_F↣_ : ℕ → ℕ → Type
n F↣ m = Σ[ f ⦂ (Fin n → Fin m) ] × ∀ {x y} → x ≢ᶠ y → f x ≢ᶠ f y

shift : (x y : Fin (suc n)) → x ≢ᶠ y → Fin n
shift         zero    (suc y) x≢y = y
shift {suc _} (suc x) zero    x≢y = zero
shift {suc _} (suc x) (suc y) x≢y = suc (shift x y x≢y)

shift-inj : ∀ (x y z : Fin (suc n)) y≢x z≢x → y ≢ᶠ z → shift x y y≢x ≢ᶠ shift x z z≢x
shift-inj         zero    (suc y) (suc z) y≢x z≢x neq = neq
shift-inj {suc _} (suc x) zero    (suc z) y≢x z≢x neq = tt
shift-inj {suc _} (suc x) (suc y) zero    y≢x z≢x neq = tt
shift-inj {suc _} (suc x) (suc y) (suc z) y≢x z≢x neq = shift-inj x y z y≢x z≢x neq

shrink : suc n F↣ suc m → n F↣ m
shrink (f , inj) .fst x = shift (f zero) (f (suc x)) (inj tt)
shrink (f , inj) .snd p = shift-inj (f zero) (f (suc _)) (f (suc _)) (inj tt) (inj tt) (inj p)


¬plus-inj : ∀ n m → ¬ (suc (n + m) F↣ m)
¬plus-inj zero    (suc m) inj       = ¬plus-inj zero m (shrink inj)
¬plus-inj (suc n) m       (f , inj) = ¬plus-inj n m (f ∘ suc , inj)
¬plus-inj zero    zero    (f , _) with f zero
... | ()

toFin-inj : (Fin n ↣ Fin m) → n F↣ m
toFin-inj f .fst = f .fst
toFin-inj (f , inj) .snd {x} {y} x≢ᶠy with x ≡ᴮ y | inspect (x ≡ᴮ_) y | f x ≡ᴮ f y | inspect (f x ≡ᴮ_) (f y)
... | false | _  | false | _  = tt
... | false | 〖 x≢y 〗 | true | 〖 fx≡fy 〗 =
  let h = inj (sound (f x) (f y) (subst T (sym fx≡fy) tt))
  in absurd (subst T x≢y (subst (T ∘ (x ≡ᴮ_)) h (complete x)))

n≢sn+m : ∀ n m → Fin n ≢ Fin (suc (n + m))
n≢sn+m n m n≡m =
  ¬plus-inj m n (toFin-inj (subst (_↣ Fin n)
                             (n≡m ⨾ cong (Fin ∘ suc) (+-comm n m))
                             (id , id)))

Fin-inj : Injective Fin
Fin-inj {n} {m} n≡m with compare n m
... | equal _ = refl
... | less    n k = absurd (n≢sn+m n k n≡m)
... | greater m k = absurd (n≢sn+m m k (sym n≡m))

compare-lt : ∀ n m → n ℕ.< suc (suc (n + m))
compare-lt zero    m = tt
compare-lt (suc n) m = compare-lt n m

compare-eq : ∀ n → n ℕ.≤ n
compare-eq zero = tt
compare-eq (suc n) = compare-eq n

↣⇒≤ : Fin n ↣ Fin m → n ℕ.≤ m
↣⇒≤ {n} {m} inj with compare n m
↣⇒≤ {n} {.(suc (n + k))} inj | less .n k = compare-lt n k
↣⇒≤ {n} {.n} inj | equal .n = compare-eq n
↣⇒≤ {.(suc (m + k))} {m} inj | greater .m k =
  absurd (¬plus-inj k m (toFin-inj (subst (_↣ _) (cong (Fin ∘ suc) (+-comm m k)) inj)))
