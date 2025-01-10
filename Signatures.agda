
{-# OPTIONS --safe #-}

module Signatures where

open import Prelude hiding (length)

--------------------------------------------------------------------------------
-- Signatures
--------------------------------------------------------------------------------

record Signature : Type₁ where
  constructor _◁_
  field  Op     : Type
         Arity  : Op → Type
⟦_⟧ : Signature → Type a → Type a
⟦ Op ◁ Arity ⟧ X = Σ[ o ⦂ Op ] × (Arity o → X)

private variable 𝔽 𝔾 ℍ : Signature

cmap : (A → B) → ⟦ 𝔽 ⟧ A → ⟦ 𝔽 ⟧ B
cmap f (o , k) = o , λ i → f (k i)

_-Alg[_] : Signature → Type a → Type a
𝔽 -Alg[ 𝒞 ] = ⟦ 𝔽 ⟧ 𝒞 → 𝒞

_-Alg : Signature → Type₁
𝔽 -Alg = Σ[ 𝒞 ⦂ Type ] × (⟦ 𝔽 ⟧ 𝒞 → 𝒞)

_⟶_ : 𝔽 -Alg → 𝔽 -Alg → Type
( 𝒞 , c ) ⟶ ( 𝒟 , d ) =
  Σ[ h ⦂ (𝒞 → 𝒟) ] × h ∘ c ≡ d ∘ cmap h

open Signature

isOfHLevelSignature : ∀ n → isOfHLevel n (𝔽 .Op) → isOfHLevel n A → isOfHLevel n (⟦ 𝔽 ⟧ A)
isOfHLevelSignature n x y = isOfHLevelΣ n x λ _ → isOfHLevelΠ n λ _ → y

infixl 6 _⊞_
_⊞_ : Signature → Signature → Signature
(𝔽 ⊞ 𝔾) .Op = 𝔽 .Op ⊎ 𝔾 .Op
(𝔽 ⊞ 𝔾) .Arity (inl  Oᶠ)  = 𝔽 .Arity Oᶠ
(𝔽 ⊞ 𝔾) .Arity (inr  Oᵍ)  = 𝔾 .Arity Oᵍ
Σ◁ : ∀ I → (I → Signature) → Signature
Σ◁ I 𝔽 .Op             = Σ[ ι ⦂ I ] × 𝔽 ι .Op
Σ◁ I 𝔽 .Arity (ι , x)  = 𝔽 ι .Arity x

_-⊞-_ : 𝔽 -Alg[ A ] → 𝔾 -Alg[ A ] → (𝔽 ⊞ 𝔾) -Alg[ A ]
(f -⊞- g) (inl o  , k) = f  (o , k)
(f -⊞- g) (inr o  , k) = g  (o , k)

inl-map : ⟦ 𝔽 ⟧ A → ⟦ 𝔽 ⊞ 𝔾 ⟧ A
inl-map (O , xs) = inl O , xs

inr-map : ⟦ 𝔾 ⟧ A → ⟦ 𝔽 ⊞ 𝔾 ⟧ A
inr-map (O , xs) = inr O , xs

syntax Σ◁ I (λ i → e) = Σ⟦ i ⦂ I ⟧ ◁ e

□ : ∀ {p} → (A → Type p) → ⟦ 𝔽 ⟧ A → Type p
□ P (_ , f) = ∀ x → P (f x)

◇ : ∀ {p} → (A → Type p) → ⟦ 𝔽 ⟧ A → Type p
◇ P (_ , f) = ∃ x × P (f x)

private variable
  xs : ⟦ 𝔽 ⟧ A

◇⇒¬□¬ : ◇ P xs → ¬ □ (¬_ ∘ P) xs
◇⇒¬□¬ (i , Pxs) ¬□¬P = ¬□¬P i Pxs

□⇒¬◇¬ : □ P xs → ¬ ◇ (¬_ ∘ P) xs
□⇒¬◇¬ □P (i , Pxs) = Pxs (□P i)

data μ (𝔽 : Signature) : Type where
  In : ⟦ 𝔽 ⟧ (μ 𝔽) → μ 𝔽

cata : (𝔽 -Alg[ A ]) → μ 𝔽 → A
cata alg (In (Oᵢ , xs)) = alg (Oᵢ , cata alg ∘ xs)

infixr 4 _⊆_
_⊆_ : Signature → Signature → Typeω
xs ⊆ ys = ∀ {ℓ} {T : Type ℓ} → ⟦ xs ⟧ T → ⟦ ys ⟧ T

infixr 4 _⊆′_
_⊆′_ : Signature → Signature → Type₁
xs ⊆′ ys = Σ[ f ⦂ Op xs ↣ Op ys ] × (∀ i → xs .Arity i ≡ ys .Arity (f .fst i))

⊆′-refl : 𝔽 ⊆′ 𝔽
⊆′-refl .fst .fst = id
⊆′-refl .fst .snd = id
⊆′-refl .snd _ = refl

⊆′-trans : 𝔽 ⊆′ 𝔾 → 𝔾 ⊆′ ℍ → 𝔽 ⊆′ ℍ
⊆′-trans fg gh .fst = ↣-trans (fg .fst) (gh .fst)
⊆′-trans fg gh .snd i = fg .snd i ⨾ gh .snd _

⊆′-inj : 𝔽 ⊆′ 𝔾 → 𝔽 ⊆ 𝔾
⊆′-inj 𝔽⊆𝔾 (O , xs) .fst = 𝔽⊆𝔾 .fst .fst O
⊆′-inj 𝔽⊆𝔾 (O , xs) .snd i = xs (transport (sym (𝔽⊆𝔾 .snd O)) i)

⊆′⊞ : 𝔽 ⊆′ 𝔽 ⊞ 𝔾
⊆′⊞ .fst .fst = inl
⊆′⊞ .fst .snd = inl-inj
⊆′⊞ .snd i = refl

module _ (𝔽 : Signature) {A : Type a} {B : Type b} (f : A → B) where
  cmap-injective : Injective f → Injective (cmap {𝔽 = 𝔽} f)
  cmap-injective inj {O₁ , k₁} {O₂ , k₂} p =
    let fst′ = cong fst p
        snd′ = cong snd p
    in cong₂ _,_ fst′
            (J
              (λ i′ q → ∀ k₂ → PathP (λ i → 𝔽 .Arity (q i) → B) (f ∘ k₁) (f ∘ k₂) → PathP (λ i → 𝔽 .Arity (q i) → A) k₁ k₂)
              (λ k₂ p → funExt λ x → inj (cong (_$ x) p))
              fst′ k₂ snd′)

open import Truth
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude using (substRefl)

module G-elim-cont (s : ⟦ 𝔽 ⟧ A)
                   (ϕ : A → Ω c)
                   (G : cmap (λ x → (x , ϕ x)) s ≡ cmap (λ x → (x , True)) s)
                   (f g : A → B)
                   (k : (x : A) → ProofOf (ϕ x) → f x ≡ g x)
                   where
  S = fst s
  t = snd s

  G″ : cmap ϕ s ≡ cmap (const True) s
  G″ = cong (cmap snd) G

  G′ : (i : 𝔽 .Arity S) → ϕ (t i) ≡ True
  G′ i = J (λ j pr → (xs : 𝔽 .Arity (pr i1) → Ω c) → PathP (λ ii → 𝔽 .Arity (pr ii) → Ω c) (snd (cmap ϕ s)) xs → snd (cmap ϕ s) i ≡ xs (subst (𝔽 .Arity) pr i))
           (λ xs pr → cong (_$ i) pr ⨾ cong xs (sym (substRefl {B = 𝔽 .Arity} i)))
           (PathPΣ G″ .fst)
           (const True)
           (PathPΣ G″ .snd)

  𝒢-elim′ : (i : 𝔽 .Arity S) → f (t i) ≡ g (t i)
  𝒢-elim′ i = k (t i) (extract (G′ i))

  𝒢-elim : cmap f s ≡ cmap g s
  𝒢-elim = cong (S ,_) (funExt 𝒢-elim′)
