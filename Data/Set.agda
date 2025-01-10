{-# OPTIONS --safe #-}
module Data.Set where

open import Prelude

infixr 5 _∷_
data 𝒦 (A : Type a) : Type a where
  _∷_ : A → 𝒦 A → 𝒦 A
  ∅ : 𝒦 A
  dup : ∀ x xs → x ∷ x ∷ xs ≡ x ∷ xs
  comm : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (𝒦 A)

data 𝔎 (A : Type a) (P : 𝒦 A → Type p) : Type (a ℓ⊔ p) where
  ∅ : 𝔎 A P
  _∷_⟨_⟩ : A → (xs : 𝒦 A) → (P⟨xs⟩ : P xs) → 𝔎 A P

embed : 𝔎 A P → 𝒦 A
embed ∅ = ∅
embed (x ∷ xs ⟨ P⟨xs⟩ ⟩) = x ∷ xs

Alg : (P : 𝒦 A → Type p) → Type _
Alg P = (xs : 𝔎 _ P) → P (embed xs)

record Coherent {A : Type a} {P : 𝒦 A → Type p} (ϕ : Alg P) : Type (a ℓ⊔ p) where
  field
    c-trunc : ∀ xs → isSet (P xs)

    c-com : ∀ x y xs P⟨xs⟩ →
            PathP
              (λ i → P (comm x y xs i))
              (ϕ (x ∷ (y ∷ xs) ⟨ ϕ (y ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩))
              (ϕ (y ∷ (x ∷ xs) ⟨ ϕ (x ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩ ))

    c-dup : ∀ x xs P⟨xs⟩ →
            PathP
              (λ i → P (dup x xs i))
              (ϕ (x ∷ (x ∷ xs) ⟨ ϕ (x ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩))
              (ϕ (x ∷ xs ⟨ P⟨xs⟩ ⟩))
open Coherent public

𝒦-foldr : (A → B → B) → B → Alg (const B)
𝒦-foldr f b ∅ = b
𝒦-foldr f b (x ∷ xs ⟨ P⟨xs⟩ ⟩) = f x P⟨xs⟩

Ψ : (𝒦 A → Type p) → Type _
Ψ P = Σ[ ϕ ⦂ Alg P ] × Coherent ϕ

Ψ-syntax : (A : Type a) → (𝒦 A → Type p) → Type _
Ψ-syntax _ = Ψ

syntax Ψ-syntax A (λ x → e) = Ψ[ x ⦂ 𝒦 A ] ↦ e

ψ : Type a → Type b → Type _
ψ A B = Ψ {A = A} (const B)

⟦_⟧ : {P : 𝒦 A → Type p} → Ψ P → (xs : 𝒦 A) → P xs
⟦ alg ⟧ ∅ = alg .fst ∅
⟦ alg ⟧ (x ∷ xs) = alg .fst (x ∷ xs ⟨ ⟦ alg ⟧ xs ⟩)
⟦ alg ⟧ (comm x y xs i) = alg .snd .c-com x y xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (dup x xs i) = alg .snd .c-dup x xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (trunc xs ys p q i j) =
  isOfHLevel→isOfHLevelDep 2
    (alg .snd .c-trunc)
    (⟦ alg ⟧ xs) (⟦ alg ⟧ ys)
    (cong ⟦ alg ⟧ p) (cong ⟦ alg ⟧ q)
    (trunc xs ys p q)
    i j

prop-coh : {A : Type a} {P : 𝒦 A → Type p} {alg : Alg P} → (∀ xs → isProp (P xs)) → Coherent alg
prop-coh P-isProp .c-trunc xs = isProp→isSet (P-isProp xs)
prop-coh {P = P} {alg = alg} P-isProp .c-dup x xs ψ⟨xs⟩ =
 toPathP (P-isProp (x ∷ xs) (transp (λ i → P (dup x xs i)) i0 (alg (x ∷ (x ∷ xs) ⟨ alg (x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))) (alg (x ∷ xs ⟨ ψ⟨xs⟩ ⟩)))
prop-coh {P = P} {alg = alg} P-isProp .c-com x y xs ψ⟨xs⟩ =
  toPathP (P-isProp (y ∷ x ∷ xs) (transp (λ i → P (comm x y xs i)) i0 (alg (x ∷ (y ∷ xs) ⟨ alg (y ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))) (alg (y ∷ (x ∷ xs) ⟨ alg (x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩)))

infix 4 _⊜_
record AnEquality (A : Type a) : Type a where
  constructor _⊜_
  field lhs rhs : 𝒦 A
open AnEquality public

EqualityProof-Alg : {B : Type b} (A : Type a) (P : 𝒦 A → AnEquality B) → Type (a ℓ⊔ b)
EqualityProof-Alg A P = Alg (λ xs → let Pxs = P xs in lhs Pxs ≡ rhs Pxs)

eq-coh : {A : Type a} {B : Type b} {P : 𝒦 A → AnEquality B} {alg : EqualityProof-Alg A P} → Coherent alg
eq-coh {P = P} = prop-coh λ xs → let Pxs = P xs in trunc (lhs Pxs) (rhs Pxs)

union-alg : ψ A (𝒦 A → 𝒦 A)
union-alg .fst ∅                  ys = ys
union-alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩)  ys = x ∷ P⟨xs⟩ ys
union-alg .snd .c-trunc _ = isSetΠ λ _ → trunc
union-alg .snd .c-com x y xs P⟨xs⟩ i ys = comm x y (P⟨xs⟩ ys) i
union-alg .snd .c-dup x xs P⟨xs⟩ i ys = dup x (P⟨xs⟩ ys) i

infixr 5 _∪_
_∪_ : 𝒦 A → 𝒦 A → 𝒦 A
_∪_ = ⟦ union-alg ⟧

∷-distrib : ∀ (x : A) xs ys → x ∷ (xs ∪ ys) ≡ xs ∪ (x ∷ ys)
∷-distrib x = ⟦ alg x ⟧
  where
  alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys → x ∷ (xs ∪ ys) ≡ xs ∪ (x ∷ ys))
  alg x .fst ∅ ys = refl
  alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) ys = comm x y (xs ∪ ys) ⨾ cong (y ∷_) (P⟨xs⟩ ys)
  alg x .snd = prop-coh λ _ → isPropΠ λ _ → trunc _ _ 

∪-idem : (xs : 𝒦 A) → xs ∪ xs ≡ xs
∪-idem = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ ((xs ∪ xs) ≡ xs)
  alg .fst ∅ = refl
  alg .snd = eq-coh
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    (x ∷ xs) ∪ (x ∷ xs) ≡˘⟨ ∷-distrib x (x ∷ xs) xs ⟩
    x ∷ x ∷ xs ∪ xs ≡⟨ dup x (xs ∪ xs) ⟩
    x ∷ xs ∪ xs ≡⟨ cong (x ∷_) P⟨xs⟩ ⟩
    x ∷ xs ∎

∪-idʳ : (xs : 𝒦 A) → (xs ∪ ∅ ≡ xs)
∪-idʳ = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (xs ∪ ∅ ≡ xs)
  alg .fst ∅ = refl
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (x ∷_) P⟨xs⟩
  alg .snd = eq-coh

∪-com : (xs ys : 𝒦 A) → (xs ∪ ys ≡ ys ∪ xs)
∪-com = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys → xs ∪ ys ≡ ys ∪ xs)
  alg .fst ∅ ys = sym (∪-idʳ ys)
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) ys = cong (x ∷_) (P⟨xs⟩ ys) ⨾ ∷-distrib x ys xs
  alg .snd = prop-coh λ _ → isPropΠ λ _ → trunc _ _

∪-assoc : (xs ys zs : 𝒦 A) → ((xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs))
∪-assoc = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys zs → (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs))
  alg .fst ∅ ys zs = refl
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) ys zs = cong (x ∷_) (P⟨xs⟩ ys zs)
  alg .snd = prop-coh λ _ → isPropΠ λ _ → isPropΠ λ _ → trunc _ _

𝒦-map : (A → B) → 𝒦 A → 𝒦 B
𝒦-map f = ⟦ map-alg f ⟧
  where
  map-alg : (A → B) → Ψ[ xs ⦂ 𝒦 A ] ↦ 𝒦 B
  map-alg f .fst ∅ = ∅
  map-alg f .fst (x ∷ _ ⟨ xs ⟩) = f x ∷ xs
  map-alg f .snd .c-trunc _ = trunc
  map-alg f .snd .c-com x y _ = comm (f x) (f y)
  map-alg f .snd .c-dup x _ = dup (f x)

map-∪ : (f : A → B) (xs ys : 𝒦 A) → 𝒦-map f xs ∪ 𝒦-map f ys ≡ 𝒦-map f (xs ∪ ys)
map-∪ f xs ys = ⟦ alg f ys ⟧ xs
  where
  alg : (f : A → B) (ys : 𝒦 A) → Ψ[ xs ⦂ 𝒦 A ] ↦ ((𝒦-map f xs ∪ 𝒦-map f ys) ≡ 𝒦-map f (xs ∪ ys))
  alg f ys .fst ∅ = refl
  alg f ys .fst (x ∷ _ ⟨ xs ⟩) = cong (f x ∷_) xs
  alg f ys .snd = prop-coh λ _ → trunc _ _

module _ {A : Type a} where
  open import Truth

  sup-sing : A → 𝒦 A → Ω a
  sup-sing x = ⟦ sup-alg x ⟧
    where
    sup-alg : A → Ψ[ xs ⦂ 𝒦 A ] ↦ Ω _
    sup-alg x .fst ∅ = True
    sup-alg x .fst (y ∷ _ ⟨ ⟅x⟆⊇xs ⟩) = (x |≡| y) |∧| ⟅x⟆⊇xs
    sup-alg x .snd .c-trunc _ = isSetΩ
    sup-alg x .snd .c-com y z _ xs = sym (∧-assoc _ _ _) ⨾ cong (_|∧| xs) (∧-com _ _ ) ⨾ ∧-assoc _ _ _
    sup-alg x .snd .c-dup y _ xs = sym (∧-assoc _ _ _) ⨾ cong (_|∧| xs) (∧-idem _)

  ⟅_⟆⊇_ : A → 𝒦 A → Type a
  ⟅ x ⟆⊇ xs = ProofOf (sup-sing x xs)

  sup-sing-∪ : (x : A) (xs ys : 𝒦 A) → ⟅ x ⟆⊇ xs → ⟅ x ⟆⊇ ys → ⟅ x ⟆⊇ (xs ∪ ys)
  sup-sing-∪ x xs ys p q = ⟦ alg x ys q ⟧ xs p
    where
    alg : (x : A) (ys : 𝒦 A) → ⟅ x ⟆⊇ ys → Ψ[ xs ⦂ 𝒦 A ] ↦ (⟅ x ⟆⊇ xs → ⟅ x ⟆⊇ (xs ∪ ys))
    alg x ys q .fst ∅ p = q
    alg x ys q .fst (y ∷ _ ⟨ P⟨xs⟩ ⟩) (p , ps) = p , P⟨xs⟩ ps
    alg x ys q .snd = prop-coh λ xs → isProp→ (IsProp (sup-sing x (xs ∪ ys)))
