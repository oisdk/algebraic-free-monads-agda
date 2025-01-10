{-# OPTIONS --safe --lossy-unification #-}

open import Prelude
open import Signatures
open import FinitenessConditions
open import FreeMonad.PackagedTheory

module Hoare.Calculus {ℓ} (𝒯 : FullTheory ℓ) where

open import FreeMonad.Quotiented 𝒯
open import Hoare.Definition 𝒯
open import Hoare.Lemmas 𝒯
open import Truth

⟨return_⟩ : Ω a → Assertion a
⟨return x ⟩ .fst = return x
⟨return x ⟩ .snd .fst k = refl
⟨return x ⟩ .snd .snd k = refl

pass : ∀ {a} → Term (Poly-⊤ {a})
pass = return Poly-tt

_<<_ : Term A → Term B → Term A
xs << ys = do x ← xs; ys; return x

sef :      (Φ : Assertion a) → let ϕ = Φ .fst in
           (q : Term A) 

    →                  SEF 0 q
    →     --------------------------------
                   ⟅ ϕ ⟆ q >> pass ⟅ ϕ ⟆

sef (ϕ , sef⟨ϕ⟩ , dsef⟨ϕ⟩) q sef⟨q⟩ .proof k =

  (do a ← ϕ
      q >> return Poly-tt
      b ← ϕ
      k Poly-tt (a |→| b)) ≡⟨ a ⇐ ϕ ⨾/ cong (_>> _) (sef⟨q⟩ _) ⟩

  (do a ← ϕ
      b ← ϕ
      k Poly-tt (a |→| b)) ≡⟨ dsef⟨ϕ⟩ (λ a b → k Poly-tt (a |→| b)) ⟩

  (do a ← ϕ
      b ← ϕ
      k Poly-tt (a |→| a)) ≡⟨ a ⇐ ϕ ⨾/ b ⇐ ϕ ⨾/ cong (k Poly-tt) (|→|-id a) ⟩

  (do a ← ϕ
      b ← ϕ
      k Poly-tt True) ≡˘⟨ a ⇐ ϕ ⨾/ cong (_>> _) (sef⟨q⟩ _) ⟩

  (do a ← ϕ
      x ← q >> return Poly-tt
      b ← ϕ
      k Poly-tt True) ∎

stateless : (ϕ : Ω a) (p : Term B) → ⟅ return ϕ ⟆ [ p /⟨⟩] ⟅ return ϕ ⟆
stateless ϕ p .proof k = cong ([ p /⟨⟩] >>_) (cong (k tt) (|→|-id ϕ))

dsef : {A : Type a}   →              (p : Term A)

                      →                  DET (ℓsuc a) p
                      → -------------------------------------------------
                          ⟅ return (True {a}) ⟆ x ← p ⟅ (do y ← p ; return (x |≡| y)) ⟆

dsef {a = aℓ} p dsef⟨p⟩ .proof k =

    (do a ← return (True {aℓ})
        x ← p
        b ← (do y ← p ; return (x |≡| y))
        k x (a |→| b)) ≡⟨⟩

    (do x ← p
        b ← (do y ← p ; return (x |≡| y))
        k x (True {aℓ} |→| b)) ≡⟨ x ⇐ p ⨾/ assoc p _ _ ⟩

    (do x ← p
        y ← p
        b ← return (x |≡| y)
        k x (True {aℓ} |→| b)) ≡⟨⟩

    (do x ← p
        y ← p
        k x (True {aℓ} |→| (x |≡| y)))

          ≡⟨ x ⇐ p ⨾/ y ⇐ p ⨾/ cong (k x) (|→|-idˡ (x |≡| y)) ⟩

    (do x ← p
        y ← p
        k x (x |≡| y)) ≡⟨ dsef⟨p⟩ _ ⟩

    (do x ← p
        y ← p
        k x (x |≡| x))

          ≡⟨ x ⇐ p ⨾/ y ⇐ p ⨾/ cong (k x) (proves ∣ refl ∣) ⟩

    (do x ← p
        y ← p
        k x (True {aℓ})) ≡˘⟨ dsef⟨p⟩ _ ⟩

    (do x ← p
        y ← p
        k x (True {aℓ})) ≡⟨⟩

    (do a ← return (True {aℓ})
        x ← p
        y ← p
        k x (True {aℓ})) ≡˘⟨ x ⇐ p ⨾/ assoc p _ _ ⟩

    (do a ← return (True {aℓ})
        x ← p
        b ← (do y ← p ; return (x |≡| y))
        k x (True {aℓ})) ∎

⟨&&&⟩ˡ :
  (ϕ : Term (Ω b))
  (ψ : A → Term (Ω b))
  (χ : Ω b)
  (t : Term A) →
  ⟅ ϕ ⟆ x ← t ⟅ ψ x ⟆ →
  ⟅ return χ ⟨∧⟩ ϕ ⟆ x ← t ⟅ return χ ⟨∧⟩ ψ x ⟆
⟨&&&⟩ˡ ϕ ψ χ t h .proof k =

  (do a ← return χ ⟨∧⟩ ϕ
      x ← t
      b ← return χ ⟨∧⟩ ψ x
      k x (a |→| b)) ≡⟨ ⟪assoc⟫ (return χ) ϕ _|∧|_ _ ⟩

  (do a ← ϕ
      x ← t
      b ← return χ ⟨∧⟩ ψ x
      k x ((χ |∧| a) |→| b)) ≡⟨ (a ⇐ ϕ ⨾/ x ⇐ t ⨾/ ⟪assoc⟫ (return χ) (ψ x) _|∧|_ _) ⟩

  (do a ← ϕ
      x ← t
      b ← ψ x
      k x ((χ |∧| a) |→| (χ |∧| b))) ≡⟨ a ⇐ ϕ ⨾/ x ⇐ t ⨾/ b ⇐ ψ x ⨾/ cong (k x) ((λ f x a → snd (f (x , a))) iff λ { f (x , a) → x , f x a }) ⟩

  (do a ← ϕ
      x ← t
      b ← ψ x
      k x (χ |→| (a |→| b))) ≡⟨ h .proof (λ x r → k x (χ |→| r)) ⟩

  (do a ← ϕ
      x ← t
      b ← ψ x
      k x (χ |→| True)) ≡⟨ a ⇐ ϕ ⨾/ x ⇐ t ⨾/ b ⇐ ψ x ⨾/ cong (k x) (|→|-annʳ χ) ⟩

  (do a ← ϕ
      x ← t
      b ← ψ x
      k x True) ≡˘⟨ a ⇐ ϕ ⨾/ x ⇐ t ⨾/ ⟪assoc⟫ (return χ) (ψ x) _|∧|_ _ ⟩

  (do a ← ϕ
      x ← t
      b ← return χ ⟨∧⟩ ψ x
      k x True) ≡˘⟨ ⟪assoc⟫ (return χ) ϕ _|∧|_ _ ⟩

  (do a ← return χ ⟨∧⟩ ϕ
      x ← t
      b ← return χ ⟨∧⟩ ψ x
      k x True) ∎

_⨾,_ : Term A → (A → Term B) → Term (A × B)
xs ⨾, ys = do
  x ← xs
  y ← ys x
  return (x , y)

⨾,-assoc : (xs : Term A) (ys : A → Term B) (k : A → B → Term C) →
           (xs ⨾, ys) >>= uncurry k ≡ (do x ← xs ; y ← ys x ; k x y)
⨾,-assoc xs ys k = assoc xs (λ x → ys x >>= λ y → return (x , y)) (uncurry k) ⨾ x ⇐ xs ⨾/ assoc (ys x) _ _

seq : {A B : Type a}

    →                (Φ : Assertion a)         → let ϕ = Φ .fst in
                     (Ψ : A → Assertion a)     → let ψ = fst ∘ Ψ in
                     (Χ : A × B → Assertion a) → let χ = fst ∘ Χ in
                            {p : Term A}    {q : A → Term B}

    →                               ⟅ ϕ ⟆ x ← p ⟅ ψ x ⟆
    →                      (∀ x → ⟅ ψ x ⟆ y ← q x ⟅ χ (x , y) ⟆)
    →              ------------------------------------------------
                             ⟅ ϕ ⟆ xy ← p ⨾, q ⟅ χ xy ⟆

seq {a = aℓ} (ϕ , sef⟨ϕ⟩ , dsef⟨ϕ⟩) Ψ Χ {p = p} {q = q} lhs rhs .proof k =

  let χ = fst ∘ Χ
      ψ = fst ∘ Ψ
  in

  (do a ← ϕ
      (x , y) ← p ⨾, q
      b ← χ (x , y)
      k (x , y) (a |→| b))

        ≡⟨ a ⇐ ϕ ⨾/ ⨾,-assoc p q _ ⟩

  (do a ← ϕ
      x ← p
      y ← q x
      b ← χ (x , y)
      k (x , y) (a |→| b))

        ≡˘⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ Ψ x .snd .fst _ ⟩

  (do a ← ϕ
      x ← p
      i ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) (a |→| b))

        ≡˘⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ i ⇐ ψ x ⨾/ y ⇐ q x ⨾/ b ⇐ χ (x , y) ⨾/ cong (k (x , y)) (|→|-idˡ _) ⟩

  (do a ← ϕ
      x ← p
      i ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) (True {aℓ} |→| (a |→| b)))

        ≡˘⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ i ⇐ ψ x ⨾/ y ⇐ q x ⨾/ sef-dsef-cont (Χ (x , y)) _ ⟩

  (do a ← ϕ
      x ← p
      i ← ψ x
      y ← q x
      b₁ ← χ (x , y)
      b₂ ← χ (x , y)
      k (x , y) (True {aℓ} |→| (a |→| b₂)))

        ≡˘⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ rhs x .proof (λ y r → do b₂ ← χ (x , y) ; k (x , y) (r |→| a |→| b₂) ) ⟩

  (do a ← ϕ
      x ← p
      i ← ψ x
      y ← q x
      b₁ ← χ (x , y)
      b₂ ← χ (x , y)
      k (x , y) ((i |→| b₁) |→| (a |→| b₂)))

        ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ i ⇐ ψ x ⨾/ y ⇐ q x ⨾/ sef-dsef-cont (Χ (x , y)) _ ⟩

  (do a ← ϕ
      x ← p
      i ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) ((i |→| b) |→| (a |→| b)))

        ≡˘⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ i ⇐ ψ x ⨾/ y ⇐ q x ⨾/ b ⇐ χ (x , y) ⨾/ cong (k (x , y)) (|→|-idˡ _) ⟩

  (do a ← ϕ
      x ← p
      i ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) (True {aℓ} |→| (i |→| b) |→| (a |→| b)))

        ≡˘⟨ sef-dsef-cont (ϕ , sef⟨ϕ⟩ , dsef⟨ϕ⟩) _ ⟩

  (do a₁ ← ϕ
      a₂ ← ϕ
      x ← p
      i ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) (True {aℓ} |→| (i |→| b) |→| (a₁ |→| b)))

        ≡˘⟨ a₁ ⇐ ϕ ⨾/ a₂ ⇐ ϕ ⨾/ x ⇐ p ⨾/ sef-dsef-cont (Ψ x) _ ⟩

  (do a₁ ← ϕ
      a₂ ← ϕ
      x ← p
      i₁ ← ψ x
      i₂ ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) (True {aℓ} |→| (i₂ |→| b) |→| (a₁ |→| b)))

        ≡˘⟨ a₁ ⇐ ϕ ⨾/ proof lhs (λ x r → do i₂ ← ψ x ; y ← q x ; b ← χ (x , y) ; k (x , y) (r |→| (i₂ |→| b) |→| (a₁ |→| b))) ⟩

  (do a₁ ← ϕ
      a₂ ← ϕ
      x ← p
      i₁ ← ψ x
      i₂ ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) ((a₂ |→| i₁) |→| (i₂ |→| b) |→| (a₁ |→| b)))

        ≡⟨ sef-dsef-cont (ϕ , sef⟨ϕ⟩ , dsef⟨ϕ⟩) _ ⟩

  (do a ← ϕ
      x ← p
      i₁ ← ψ x
      i₂ ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) ((a |→| i₁) |→| (i₂ |→| b) |→| (a |→| b)))

        ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ sef-dsef-cont (Ψ x) _ ⟩

  (do a ← ϕ
      x ← p
      i ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) ((a |→| i) |→| (i |→| b) |→| (a |→| b)))

        ≡˘⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ i ⇐ ψ x ⨾/ y ⇐ q x ⨾/ b ⇐ χ (x , y) ⨾/ cong (k (x , y)) (|→|-curry _ _ _) ⟩

  (do a ← ϕ
      x ← p
      i ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) ((a |→| i) |∧| (i |→| b) |→| (a |→| b)))

        ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ i ⇐ ψ x ⨾/ y ⇐ q x ⨾/ b ⇐ χ (x , y) ⨾/ cong (k (x , y)) (|→|-trans a i b) ⟩

  (do a ← ϕ
      x ← p
      i ← ψ x
      y ← q x
      b ← χ (x , y)
      k (x , y) (True {aℓ}))

        ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ Ψ x .snd .fst _ ⟩

  (do a ← ϕ
      x ← p
      y ← q x
      b ← χ (x , y)
      k (x , y) True)

        ≡˘⟨ a ⇐ ϕ ⨾/ ⨾,-assoc p q _ ⟩

  (do a ← ϕ
      (x , y) ← p ⨾, q
      b ← χ (x , y)
      k (x , y) True) ∎



focus : {A B : Type a} {ϕ : Term (Ω b)} {ψ : B → Term (Ω c)} {p : Term A}
      → (sub : A → B)
      → ⟅ ϕ ⟆ x ← p ⟅ ψ (sub x) ⟆
      → ⟅ ϕ ⟆ x ← sub <$> p ⟅ ψ x ⟆
focus {ϕ = ϕ} {ψ = ψ} {p = p} sub hr .proof k =
  (do a ← ϕ
      x ← sub <$> p
      b ← ψ x
      k x (a |→| b)) ≡⟨ a ⇐ ϕ ⨾/ assoc p _ _ ⟩

  (do a ← ϕ
      x ← p
      b ← ψ (sub x)
      k (sub x) (a |→| b)) ≡⟨ hr .proof (k ∘ sub) ⟩

  (do a ← ϕ
      x ← p
      b ← ψ (sub x)
      k (sub x) True) ≡˘⟨ a ⇐ ϕ ⨾/ assoc p _ _ ⟩

  (do a ← ϕ
      x ← sub <$> p
      b ← ψ x
      k x True) ∎

≡⟅≡⟆≡ : {ϕ ϕ′ : Term (Ω a)} {t t′ : Term A} {ψ ψ′ : A → Term (Ω b)} → ϕ ≡ ϕ′ → t ≡ t′ → (∀ x → ψ x ≡ ψ′ x) → ⟅ ϕ ⟆ x ← t ⟅ ψ x ⟆ → ⟅ ϕ′ ⟆ x ← t′ ⟅ ψ′ x ⟆
≡⟅≡⟆≡ p q r = subst (Hoare _ _) (funExt r) ∘ subst₂ (λ x y → Hoare x y _) p q

subst-⟅⟆ : {ϕ : Term (Ω b)} {p : Term A} {ψ : A → Term (Ω c)} {q : Term A}
        → p ≡ q
        → ⟅ ϕ ⟆ x ← p ⟅ ψ x ⟆
        → ⟅ ϕ ⟆ x ← q ⟅ ψ x ⟆
subst-⟅⟆ {ϕ = ϕ} {ψ = ψ} = subst (flip (Hoare ϕ) ψ)

seq′ : {A B : Type a}
    →                (Φ : Assertion a)     → let ϕ = Φ .fst in
                     (Ψ : A → Assertion a) → let ψ = fst ∘ Ψ in
                     (Χ : B → Assertion a) → let χ = fst ∘ Χ in
                            {p : Term A}    {q : A → Term B}

    →                               ⟅ ϕ ⟆ x ← p ⟅ ψ x ⟆
    →                      (∀ x → ⟅ ψ x ⟆ y ← q x ⟅ χ y ⟆)
    →              ------------------------------------------------
                             ⟅ ϕ ⟆ y ← p >>= q ⟅ χ y ⟆
seq′ Φ Ψ Χ {p = p} {q = q} lhs rhs =
  let h  = seq Φ Ψ (Χ ∘ snd) lhs rhs
      h′ = focus snd h
  in subst-⟅⟆ (snd <$> (p ⨾, q) ≡⟨ assoc p  _ _ ⨾ x ⇐ p ⨾/ assoc (q x) _ _ ⨾ >>=-idʳ (q x) ⟩ (p >>= q) ∎) h′

seq⁻ : {A B : Type a}
    →                (Φ : Assertion a)     → let ϕ = Φ .fst in
                     (Ψ : A → Assertion a) → let ψ = fst ∘ Ψ in
                     (Χ : B → Assertion a) → let χ = fst ∘ Χ in
                            {p : Term A}    {q : A → Term B}

    →                      (∀ x → ⟅ ψ x ⟆ y ← q x ⟅ χ y ⟆)
    →                               ⟅ ϕ ⟆ x ← p ⟅ ψ x ⟆
    →              ------------------------------------------------
                             ⟅ ϕ ⟆ y ← p >>= q ⟅ χ y ⟆
seq⁻ Φ Ψ Χ = flip (seq′ Φ Ψ Χ)

seq-<< : {A B : Type a}
    →                (Φ : Assertion a)     → let ϕ = Φ .fst in
                     (Ψ : A → Assertion a) → let ψ = fst ∘ Ψ in
                     (Χ : A → Assertion a) → let χ = fst ∘ Χ in
                            {p : Term A}    {q : Term B}

    →                               ⟅ ϕ ⟆ x ← p ⟅ ψ x ⟆
    →                      (∀ x → ⟅ ψ x ⟆ y ← q ⟅ χ x ⟆)
    →              ------------------------------------------------
                             ⟅ ϕ ⟆ y ← p << q ⟅ χ y ⟆
seq-<< Φ Ψ Χ {p = p} {q = q} lhs rhs =
  let h = seq Φ Ψ (Χ ∘ fst) lhs rhs
      h′ = focus fst h
  in subst-⟅⟆ (assoc p _ _ ⨾ x ⇐ p ⨾/ assoc q _ _) h′


module _
  {A : Type a}
  (ϕ : Assertion a)
  (p : Term A)
  (ψ χ : A → Assertion a)
  where
    imply : (∀ x → ⟅ ψ x .fst ⟆ pass ⟅ χ x .fst ⟆)
          → ⟅ ϕ .fst ⟆ x ← p ⟅ ψ x .fst ⟆
          → ⟅ ϕ .fst ⟆ x ← p ⟅ χ x .fst ⟆
    imply imp h = subst-⟅⟆ (>>=-idʳ p) ( seq′ ϕ ψ χ h λ x → focus (const x) (imp x))

⟅snd⟆ : {A : Type a} (Φ : Assertion a) (p : Term A)
        (ψ₁ : A → Term (Ω a)) →
        (sef⟨ψ₁⟩ : ∀ x → SEF (ℓsuc a) (ψ₁ x))
        (Ψ₂ : A → Assertion a) →
      ⟅ Φ .fst ⟆ x ← p ⟅ ψ₁ x ⟨∧⟩ Ψ₂ x .fst ⟆ → ⟅ Φ .fst ⟆ x ← p ⟅ Ψ₂ x .fst ⟆
⟅snd⟆ Φ p ψ₁ sef⟨ψ₁⟩ Ψ₂ prf .proof k =
  let ϕ = Φ .fst
      ψ₂ = fst ∘ Ψ₂
  in

  (do a ← ϕ
      x ← p
      b₂ ← ψ₂ x
      k x (a |→| b₂)) ≡˘⟨ a ⇐ ϕ ⨾/ Φ .snd .fst _ ⟩

  (do a ← ϕ
      a′ ← ϕ
      x ← p
      b₂ ← ψ₂ x
      k x (a |→| b₂)) ≡˘⟨ a ⇐ ϕ ⨾/ a′ ⇐ ϕ ⨾/ x ⇐ p ⨾/ sef⟨ψ₁⟩ x _ ⟩

  (do a ← ϕ
      a′ ← ϕ
      x ← p
      b₁′ ← ψ₁ x
      b₂ ← ψ₂ x
      k x (a |→| b₂)) ≡˘⟨ a ⇐ ϕ ⨾/ a′ ⇐ ϕ ⨾/ x ⇐ p ⨾/ b₁′ ⇐ ψ₁ x ⨾/ Ψ₂ x .snd .fst _ ⟩

  (do a ← ϕ
      a′ ← ϕ
      x ← p
      b₁′ ← ψ₁ x
      b₂′ ← ψ₂ x
      b₂ ← ψ₂ x
      k x (a |→| b₂)) ≡˘⟨ a ⇐ ϕ ⨾/ a′ ⇐ ϕ ⨾/ x ⇐ p ⨾/ ⟪assoc⟫ (ψ₁ x) (ψ₂ x) _|∧|_ _ ⟩

  (do a ← ϕ
      a′ ← ϕ
      x ← p
      b′ ← ψ₁ x ⟨∧⟩ ψ₂ x
      b₂ ← ψ₂ x
      k x (a |→| b₂)) ≡⟨ a ⇐ ϕ ⨾/ a′ ⇐ ϕ ⨾/ x ⇐ p ⨾/ b′ ⇐ ψ₁ x ⟨∧⟩ ψ₂ x ⨾/ b₂ ⇐ ψ₂ x ⨾/ cong (k x) (cong (a |→|_) ((_, _) iff fst)) ⟩

  (do a ← ϕ
      a′ ← ϕ
      x ← p
      b′ ← ψ₁ x ⟨∧⟩ ψ₂ x
      b₂ ← ψ₂ x
      k x (a |→| (b₂ |∧| True))) ≡˘⟨ a ⇐ ϕ ⨾/  prf .proof (λ x t → do b₂ ← ψ₂ x; k x (a |→| (b₂ |∧| t))) ⟩

  (do a ← ϕ
      a′ ← ϕ
      x ← p
      b′ ← ψ₁ x ⟨∧⟩ ψ₂ x
      b₂ ← ψ₂ x
      k x (a |→| (b₂ |∧| (a′ |→| b′)))) ≡⟨ sef-dsef-cont Φ _ ⟩

  (do a ← ϕ
      x ← p
      b′ ← ψ₁ x ⟨∧⟩ ψ₂ x
      b₂ ← ψ₂ x
      k x (a |→| (b₂ |∧| (a |→| b′)))) ≡⟨ (a ⇐ ϕ ⨾/ x ⇐ p ⨾/ ⟪assoc⟫ (ψ₁ x) (ψ₂ x) _|∧|_ _ ) ⟩

  (do a ← ϕ
      x ← p
      b₁ ← ψ₁ x
      b₂′ ← ψ₂ x
      b₂ ← ψ₂ x
      k x (a |→| (b₂ |∧| (a |→| (b₁ |∧| b₂′))))) ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ b₁ ⇐ ψ₁ x ⨾/ sef-dsef-cont (Ψ₂ x) _ ⟩

  (do a ← ϕ
      x ← p
      b₁ ← ψ₁ x
      b₂ ← ψ₂ x
      k x (a |→| (b₂ |∧| (a |→| (b₁ |∧| b₂))))) ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ b₁ ⇐ ψ₁ x ⨾/ b₂ ⇐ ψ₂ x ⨾/ cong (k x) ((λ f x → f x .snd x .fst , f x .fst) iff λ f x → f x .snd , const (f x)) ⟩

  (do a ← ϕ
      x ← p
      b₁ ← ψ₁ x
      b₂ ← ψ₂ x
      k x (a |→| (b₁ |∧| b₂))) ≡˘⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ ⟪assoc⟫ (ψ₁ x) (ψ₂ x) _|∧|_ _ ⟩

  (do a ← ϕ
      x ← p
      b₁∧b₂ ← ψ₁ x ⟨∧⟩ ψ₂ x
      k x (a |→| b₁∧b₂)) ≡⟨ prf .proof k ⟩

  (do a ← ϕ
      x ← p
      b₁∧b₂ ← ψ₁ x ⟨∧⟩ ψ₂ x
      k x True) ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ ⟪assoc⟫ (ψ₁ x) (ψ₂ x) _|∧|_ _ ⟩

  (do a ← ϕ
      x ← p
      b₁ ← ψ₁ x
      b₂ ← ψ₂ x
      k x True) ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/  sef⟨ψ₁⟩ x _ ⟩


  (do a ← ϕ
      x ← p
      b₂ ← ψ₂ x
      k x True) ∎

⟅→⟆True : (ϕ : Term (Ω a)) (t : Term B) → ⟅ ϕ ⟆ _ ← t ⟅ return (True {ℓ = c}) ⟆
⟅→⟆True ϕ t .proof k = a ⇐ ϕ ⨾/ x ⇐ t ⨾/ cong (k x) (|→|-annʳ _)


module _ {A : Type a} (Φ : Assertion a) {t : Term A} {ψ : A → Term (Ω a)} (f : Ω a → Ω a) where
  private ϕ = fst Φ

  →⟅∙⟆ : (i : ∀ {x} → ProofOf (f x) → ProofOf x)
       → ⟅ ϕ ⟆ x ← t ⟅ ψ x ⟆
       → ⟅ f <$> ϕ ⟆ x ← t ⟅ ψ x ⟆
  →⟅∙⟆ i h .proof k =
    (do a ← f <$> ϕ
        x ← t
        b ← ψ x
        k x (a |→| b))

      ≡⟨ assoc ϕ _ _ ⟩

    (do a ← ϕ
        x ← t
        b ← ψ x
        k x (f a |→| b))

      ≡⟨ a ⇐ ϕ ⨾/ x ⇐ t ⨾/ b ⇐ ψ x ⨾/ cong (k x) ((λ k x y → k x) iff λ k x → k x (i x)) ⟩

    (do a ← ϕ
        x ← t
        b ← ψ x
        k x (f a |→| a |→| b))

      ≡˘⟨ sef-dsef-cont Φ _ ⟩

    (do a  ← ϕ
        a′ ← ϕ
        x ← t
        b ← ψ x
        k x (f a |→| a′ |→| b))

      ≡⟨ a ⇐ ϕ ⨾/ h .proof (λ x r → k x (f a |→| r)) ⟩

    (do a  ← ϕ
        a′ ← ϕ
        x ← t
        b ← ψ x
        k x (f a |→| True))

      ≡⟨ sef-dsef-cont Φ _ ⟩

    (do a ← ϕ
        x ← t
        b ← ψ x
        k x (f a |→| True))

      ≡⟨ a ⇐ ϕ ⨾/ x ⇐ t ⨾/ b ⇐ ψ x ⨾/ cong (k x) (|→|-annʳ (f a)) ⟩

    (do a ← ϕ
        x ← t
        b ← ψ x
        k x True)

      ≡˘⟨ assoc ϕ _ _ ⟩

    (do a ← f <$> ϕ
        x ← t
        b ← ψ x
        k x True) ∎

module _ {A : Type a} (Φ : Assertion a) {t : Term A} (Ψ : A → Assertion a) (f : Ω a → Ω a) where
  private
    ψ = fst ∘ Ψ
    ϕ = fst Φ

  ⟅∙⟆→ : (i : ∀ {x} → ProofOf x → ProofOf (f x))
       → ⟅ ϕ ⟆ x ← t ⟅ ψ x ⟆
       → ⟅ ϕ ⟆ x ← t ⟅ f <$> ψ x ⟆
  ⟅∙⟆→ i h =
    subst-⟅⟆ (>>=-idʳ _) (seq′ Φ Ψ (λ x → _ ,  sef-<$> f (ψ x) (Ψ x .snd .fst) , det-<$> f (ψ x) (Ψ x .snd .snd)) h
      λ where x .proof k →
                            (do a ← ψ x
                                b ← f <$> ψ x
                                k _ (a |→| b)) ≡⟨ a ⇐ ψ x ⨾/ assoc (ψ x) _ _ ⟩

                            (do a ← ψ x
                                b ← ψ x
                                k _ (a |→| f b)) ≡⟨ sef-dsef-cont (Ψ x) _ ⟩

                            (do a ← ψ x
                                k _ (a |→| f a)) ≡⟨ a ⇐ ψ x ⨾/ cong (k _) (proves i) ⟩

                            (do a ← ψ x
                                k _ True) ≡˘⟨ Ψ x .snd .fst _ ⟩

                            (do a ← ψ x
                                b ← ψ x
                                k _ True) ≡˘⟨ a ⇐ ψ x ⨾/ assoc (ψ x) _ _ ⟩

                            (do a ← ψ x
                                b ← f <$> ψ x
                                k _ True) ∎
        )



False⟅→⟆ : (t : Term A) (ϕ : A → Term (Ω b)) → ⟅ return (False {ℓ = c}) ⟆ x ← t ⟅ ϕ x ⟆
False⟅→⟆ t ϕ .proof k = x ⇐ t ⨾/ b ⇐ ϕ x ⨾/ cong (k x) (|→|-annˡ _)

⟅id⟆ : (ϕ : Term (Ω a)) → DET (ℓsuc a) ϕ → ⟅ ϕ ⟆ pass {a = a} ⟅ ϕ ⟆
⟅id⟆ ϕ det .proof k = det (λ a b → k Poly-tt (a |→| b)) ⨾ a ⇐ ϕ ⨾/ b ⇐ ϕ ⨾/ cong (k Poly-tt) (|→|-id _)

⟅ret⟆ : (ϕ : Ω a) (t : Term B) → ⟅ return ϕ ⟆ _ ← t ⟅ return ϕ ⟆
⟅ret⟆ ϕ t .proof k = x ⇐ t ⨾/ cong (k x) (|→|-id ϕ)

≡⟅∙⟆≡ : {ϕ ϕ′ : Term (Ω a)} {t : Term A} {ψ ψ′ : A → Term (Ω b)} → ϕ ≡ ϕ′ → (∀ x → ψ x ≡ ψ′ x) → ⟅ ϕ ⟆ x ← t ⟅ ψ x ⟆ → ⟅ ϕ′ ⟆ x ← t ⟅ ψ′ x ⟆
≡⟅∙⟆≡ {t = t} p q = subst₂ (λ p q → Hoare p t q) p (funExt q)

≡⟅∙⟆ : {ϕ ϕ′ : Term (Ω a)} {t : Term A} {ψ : A → Term (Ω b)} → ϕ ≡ ϕ′ → ⟅ ϕ ⟆ x ← t ⟅ ψ x ⟆ → ⟅ ϕ′ ⟆ x ← t ⟅ ψ x ⟆
≡⟅∙⟆ {t = t} {ψ = ψ} = subst (λ p → Hoare p t ψ)

⟅∙⟆≡ : {ϕ : Term (Ω a)} {t : Term A} {ψ ψ′ : A → Term (Ω b)} → (∀ x → ψ x ≡ ψ′ x) → ⟅ ϕ ⟆ x ← t ⟅ ψ x ⟆ → ⟅ ϕ ⟆ x ← t ⟅ ψ′ x ⟆
⟅∙⟆≡ {ϕ = ϕ} {t = t} e = subst (λ p → Hoare ϕ t p) (funExt e)

⟨&&&⟩ʳ :
  (ϕ : Term (Ω b))
  (ψ : A → Term (Ω b))
  (χ : Ω b)
  (t : Term A) →
  ⟅ ϕ ⟆ x ← t ⟅ ψ x ⟆ →
  ⟅ ϕ ⟨∧⟩ return χ ⟆ x ← t ⟅ ψ x ⟨∧⟩ return χ ⟆
⟨&&&⟩ʳ ϕ ψ χ t h = ≡⟅∙⟆≡ (a ⇐ ϕ ⨾/ cong return (∧-com χ a)) (λ x → b ⇐ ψ x ⨾/ cong return (∧-com χ b)) (⟨&&&⟩ˡ ϕ ψ χ t h)

False⟨∧⟩ : (ϕ : Term (Ω a)) → SEF (ℓsuc a) ϕ → return False ⟨∧⟩ ϕ ≡ return False
False⟨∧⟩ ϕ sef =
  return False ⟨∧⟩ ϕ ≡⟨⟩
  (do f ← return False; p ← ϕ; return (f |∧| p)) ≡⟨⟩
  (do p ← ϕ; return (False |∧| p)) ≡⟨ p ⇐ ϕ ⨾/ cong return (fst iff λ ()) ⟩
  (do p ← ϕ; return False) ≡⟨ sef (return False) ⟩
  return False ∎

True⟨∧⟩ : (ϕ : Term (Ω a)) → return True ⟨∧⟩ ϕ ≡ ϕ
True⟨∧⟩ ϕ = (a ⇐ ϕ ⨾/ cong return (∧-id a)) ⨾ <$>-id ϕ


weaken : {A : Type a}
       → (Φ : Assertion a) → let ϕ = Φ .fst in
         (Ψ : A → Assertion a) → let ψ = fst ∘ Ψ in
         {p : Term A}
       → (Χ : Assertion a) → let χ = Χ .fst in
         ⟅ χ ⟆ pass ⟅ ϕ ⟆
       → ⟅ ϕ ⟆ x ← p ⟅ ψ x ⟆
       → ⟅ χ ⟆ x ← p ⟅ ψ x ⟆
weaken Φ Ψ {p = p} Χ lhs rhs =
  let h = seq Χ (λ _ → Φ) (λ { (_ , x) → Ψ x }) lhs (λ _ → rhs)
      h′ = focus snd h
  in subst-⟅⟆ (assoc (return Poly-tt) (λ x → p >>= λ y → return (x , y)) (return ∘′ snd) ⨾ assoc p _ _ ⨾ >>=-idʳ p) h′

if : {A : Type a}
   →                    (ϕ : Term (Ω a)) (ψ : A → Term (Ω a)) 
   →
   (p : Term A) (q : Term A) (b : Bool) →
   ⟅ return (|T|     b)  ⟨∧⟩ ϕ ⟆ x ← p ⟅ ψ x ⟆ →
   ⟅ return (|T| (!  b)) ⟨∧⟩ ϕ ⟆ x ← q ⟅ ψ x ⟆ →    
   ⟅ ϕ ⟆ x ← if b then p else q ⟅ ψ x ⟆

if ϕ ψ p q =
  bool 
    (λ _ rhs → subst (λ e → ⟅ e ⟆ x ← q ⟅ ψ x ⟆) (∧-lemma ϕ) rhs)
    (λ lhs _ → subst (λ e → ⟅ e ⟆ x ← p ⟅ ψ x ⟆) (∧-lemma ϕ) lhs)
    where
    ∧-lemma : (x : Term (Ω a)) → (True |∧|_) <$> x ≡ x
    ∧-lemma x = cong (_<$> x) (funExt ∧-id) ⨾ <$>-id x

conj : {A : Type a}
     →                 (Φ : Assertion a) → let ϕ = fst Φ in
                       (ψ : A → Term (Ω a)) → (∀ x → SEF (ℓsuc a) (ψ x))
     →                 (χ : A → Term (Ω a)) 
     →                              (p : Term A)
     →
      (⟅ ϕ ⟆ x ← p ⟅ ψ x ⟆) → (⟅ ϕ ⟆ x ← p ⟅ χ x ⟆) → (⟅ ϕ ⟆ x ← p ⟅ ψ x ⟨∧⟩ χ x ⟆)

conj {a = aℓ} (ϕ , sef⟨ϕ⟩ , dsef⟨ϕ⟩) ψ sef⟨ψ⟩ χ p lhs rhs .proof k =

  (do a ← ϕ
      x ← p
      b ← (ψ x ⟨∧⟩ χ x)
      k x (a |→| b)) ≡⟨⟩

  (do a ← ϕ
      x ← p
      b ← (do b₁ ← ψ x ; b₂ ← χ x ; return (b₁ |∧| b₂))
      k x (a |→| b)) ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ assoc (ψ x) _ _ ⨾ b₁ ⇐ ψ x ⨾/ assoc (χ x) _ _ ⟩

  (do a ← ϕ
      x ← p
      b₁ ← ψ x
      b₂ ← χ x
      k x (a |→| (b₁ |∧| b₂)))

        ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ b₁ ⇐ ψ x ⨾/ b₂ ⇐ χ x ⨾/ cong (k x) (|→|-|∧| a b₁ b₂) ⟩

  (do a ← ϕ
      x ← p
      b₁ ← ψ x
      b₂ ← χ x
      k x ((a |→| b₁) |∧| (a |→| b₂)))

      ≡˘⟨ sef-dsef-cont (ϕ , sef⟨ϕ⟩ , dsef⟨ϕ⟩) _ ⟩

  (do a₁ ← ϕ
      a₂ ← ϕ
      x ← p
      b₁ ← ψ x
      b₂ ← χ x
      k x ((a₂ |→| b₁) |∧| (a₁ |→| b₂)))

      ≡⟨ a₁ ⇐ ϕ ⨾/ lhs .proof (λ x r → do b₂ ← χ x ; k x (r |∧| (a₁ |→| b₂))) ⟩

  (do a₁ ← ϕ
      a₂ ← ϕ
      x ← p
      ψ x
      b₂ ← χ x
      k x (True {aℓ} |∧| (a₁ |→| b₂))) ≡⟨ sef-dsef-cont (ϕ , sef⟨ϕ⟩ , dsef⟨ϕ⟩) _ ⟩

  (do a ← ϕ
      x ← p
      ψ x
      b₂ ← χ x
      k x (True {aℓ} |∧| (a |→| b₂)))

        ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ _ ⇐ ψ x ⨾/ b₂ ⇐ χ x ⨾/ cong (k x) (∧-id _) ⟩

  (do a ← ϕ
      x ← p
      ψ x
      b₂ ← χ x
      k x (a |→| b₂)) ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ sef⟨ψ⟩ x _ ⟩

  (do a ← ϕ
      x ← p
      b₂ ← χ x
      k x (a |→| b₂)) ≡⟨ rhs .proof k ⟩

  (do a ← ϕ
      x ← p
      χ x
      k x True) ≡˘⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ sef⟨ψ⟩ x _ ⟩

  (do a ← ϕ
      x ← p
      ψ x
      χ x
      k x True) ≡˘⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ assoc (ψ x) _ _ ⨾ b ⇐ ψ x ⨾/ assoc (χ x) _ _ ⟩

  (do a ← ϕ
      x ← p
      ψ x ⟨∧⟩ χ x
      k x True) ∎

⟅∧⟆ : {A : Type a} {p : Ω a} (ϕ : Assertion a) {t : Term A} (ψ : A → Assertion a)
   → ⟅ ϕ .fst ⟆ x ← t ⟅ ψ x .fst ⟆ → ⟅ return p ⟨∧⟩ ϕ .fst ⟆ x ← t ⟅ return p ⟨∧⟩ ψ x .fst ⟆
⟅∧⟆ {p = p} ϕ {t = t} ψ rhs =
  conj
    (return p ⟨∧⟩ ϕ .fst , sef-<$> _ _ (ϕ .snd .fst) , det-<$> _ _ (ϕ .snd .snd))
    (λ _ → return p)
    ( λ x k → refl)
    (λ x → ψ x .fst)
    t
    (λ where .proof k → (do a ← return p ⟨∧⟩ ϕ .fst; x ← t; b ← return p; k x (a |→| b)) ≡⟨ assoc (ϕ .fst) _ _ ⟩
                        (do a ← ϕ .fst; x ← t; b ← return p; k x ((p |∧| a) |→| b)) ≡⟨⟩
                        (do a ← ϕ .fst; x ← t; k x ((p |∧| a) |→| p)) ≡⟨ a ⇐ ϕ .fst ⨾/ x ⇐ t ⨾/ cong (k x) (proves fst) ⟩
                        (do a ← ϕ .fst; x ← t; k x True) ≡˘⟨ assoc (ϕ .fst) _ _ ⟩
                        (do a ← return p ⟨∧⟩ ϕ .fst; x ← t; b ← return p; k x True) ∎
    )
    (→⟅∙⟆ (_ , ϕ .snd .fst ,  ϕ .snd .snd) _ snd rhs)

module _ {A : Type a} where
  disj :                    (ϕ : Term (Ω a))
       →                    (ψ : Term (Ω a)) → SEF (ℓsuc a) ψ
       →                    (Χ : A → Assertion a) → let χ = fst ∘ Χ in 
                            (p : Term A)
       →
       (⟅ ϕ ⟆ x ← p ⟅ χ x ⟆) → (⟅ ψ ⟆ x ← p ⟅ χ x ⟆) → (⟅ ϕ ⟨∨⟩ ψ ⟆ x ← p ⟅ χ x ⟆)
  disj ϕ ψ sef⟨ψ⟩ Χ p lhs rhs .proof k = let χ = fst ∘ Χ in
    (do a ← ϕ ⟪ _|∨|_ ⟫ ψ
        x ← p
        b ← χ x
        k x (a |→| b)) ≡⟨ ⟪assoc⟫ ϕ ψ _|∨|_ _ ⟩
  
    (do a₁ ← ϕ
        a₂ ← ψ
        x ← p
        b ← χ x
        k x (a₁ |∨| a₂ |→| b))
  
          ≡⟨ a₁ ⇐ ϕ ⨾/ a₂ ⇐ ψ ⨾/ x  ⇐ p ⨾/ b  ⇐ χ x ⨾/ cong (k x) (|∨|-|→| _ _ _) ⟩
  
    (do a₁ ← ϕ
        a₂ ← ψ
        x ← p
        b ← χ x
        k x ((a₁ |→| b) |∧| (a₂ |→| b))) ≡˘⟨ a₁ ⇐ ϕ ⨾/ a₂ ⇐ ψ ⨾/ x ⇐ p ⨾/ sef-dsef-cont (Χ x) _ ⟩
  
    (do a₁ ← ϕ
        a₂ ← ψ
        x ← p
        b₁ ← χ x
        b₂ ← χ x
        k x ((a₁ |→| b₂) |∧| (a₂ |→| b₁))) ≡⟨ a₁ ⇐ ϕ ⨾/ rhs .proof (λ x r → χ x >>= λ b₂ → k x ((a₁ |→| b₂) |∧| r)) ⟩
  
    (do a₁ ← ϕ
        a₂ ← ψ
        x ← p
        b₁ ← χ x
        b₂ ← χ x
        k x ((a₁ |→| b₂) |∧| True)) ≡⟨ a₁ ⇐ ϕ ⨾/ sef⟨ψ⟩ _ ⟩
  
    (do a ← ϕ
        x ← p
        b₁ ← χ x
        b₂ ← χ x
        k x ((a |→| b₂) |∧| True)) ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ sef-dsef-cont (Χ x) _ ⟩
  
    (do a ← ϕ
        x ← p
        b ← χ x
        k x ((a |→| b) |∧| True)) ≡⟨ a ⇐ ϕ ⨾/ x ⇐ p ⨾/ b ⇐ χ x ⨾/ cong (k x) (∧-com _ _ ⨾ ∧-id _) ⟩
  
    (do a ← ϕ
        x ← p
        b ← χ x
        k x (a |→| b)) ≡⟨ lhs .proof k ⟩
  
    (do a ← ϕ
        x ← p
        b ← χ x
        k x True) ≡˘⟨ a ⇐ ϕ ⨾/ sef⟨ψ⟩ _ ⟩
  
    (do a₁ ← ϕ
        a₂ ← ψ
        x ← p
        b ← χ x
        k x True) ≡˘⟨ ⟪assoc⟫ ϕ ψ _|∨|_ _ ⟩
  
    (do a ← ϕ ⟪ _|∨|_ ⟫ ψ
        x ← p
        b ← χ x
        k x True) ∎
