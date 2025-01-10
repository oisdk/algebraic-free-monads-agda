{-# OPTIONS --safe #-}

module Finite.OnLists where

open import Prelude
open import Data.List
open import Data.List.Membership

ℰ! : Type a → Type a
ℰ! A = Σ[ xs ⦂ List A ] × (∀ x → x ∈ xs)

sup-Σ :  List A →
         ((x : A) → List (P x)) →
         List (Σ A P)
sup-Σ xs ys = concatMap (λ x → mapl (x ,_) (ys x)) xs

cov-Σ : (x : A)
      → (y : P x)
      → (xs : List A)
      → (ys : ∀ x → List (P x))
      → x ∈ xs
      → y ∈ ys x
      → (x , y) ∈ sup-Σ xs ys
cov-Σ xᵢ yᵢ (x ∷ xs) ys (suc n , x∈xs) y∈ys =
  mapl (x ,_) (ys x) ++◇ cov-Σ xᵢ yᵢ xs ys (n , x∈xs) y∈ys
cov-Σ xᵢ yᵢ (x ∷ xs) ys (zero  , x∈xs) y∈ys =
  subst (λ x′ → (xᵢ , yᵢ) ∈ sup-Σ (x′ ∷ xs) ys) (sym x∈xs)
  (mapl (xᵢ ,_) (ys xᵢ) ◇++ cong-∈ _ (ys xᵢ) y∈ys)

_|Σ|_ : ℰ! A → (∀ x → ℰ! (P x)) → ℰ! (Σ A P)
(xs |Σ| ys) .fst = sup-Σ (xs .fst) (fst ∘′ ys)
(xs |Σ| ys) .snd (x , y) = cov-Σ x y (xs .fst) (fst ∘′ ys) (xs .snd x) (ys x .snd y)

ℬ : Type a → Type a
ℬ A = Σ[ xs ⦂ List A ] × ∀ x → x ∈! xs

ℰ!⇒Discrete : ℰ! A → Discrete A
ℰ!⇒Discrete e x y with e .snd x | inspect (e .snd) x | e .snd y | inspect (e .snd) y
... | i , p | 〖 ex 〗 | j , q | 〖 ey 〗 with discreteFin i j
... | yes i≡j = yes (sym p ⨾ cong (e .fst !!_) i≡j ⨾ q)
... | no  i≢j = no λ x≡y → i≢j (cong fst (sym ex) ⨾ cong (fst ∘′ e .snd) x≡y ⨾ cong fst ey)

ℰ!⇒ℬ : ℰ! A → ℬ A
ℰ!⇒ℬ xs = λ where
    .fst → uniques disc (xs .fst)
    .snd x → ∈⇒∈! disc x (xs .fst) (xs .snd x)
  where
  disc = ℰ!⇒Discrete xs

ℱ : Type a → Type a
ℱ A = ∃ n × (Fin n ≃ A)

ℬ→ℱ : ℬ A → ℱ A
ℬ→ℱ (xs , f) .fst = length xs
ℬ→ℱ (xs , f) .snd .fst = xs !!_
ℬ→ℱ (xs , f) .snd .snd .equiv-proof = f
