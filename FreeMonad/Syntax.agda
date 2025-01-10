
{-# OPTIONS --safe #-}

open import Signatures
open import Prelude hiding (Iso)

module FreeMonad.Syntax (𝔽 : Signature) where

open Signature 𝔽

--------------------------------------------------------------------------------
-- Unquotiented Free Monad
--------------------------------------------------------------------------------

data Syntax (ν : Type a) : Type a where
  var  : ν                 → Syntax ν
  op   : ⟦ 𝔽 ⟧ (Syntax ν)  → Syntax ν

Op⟦_⟧ : ∀ o → Syntax (Arity o)
Op⟦ o ⟧ = op (o , var)

private variable ν : Type a

syntax-alg : 𝔽 -Alg[ Syntax ν ]
syntax-alg = op
syntax-alg' : (v : Type) → 𝔽 -Alg
syntax-alg' ν = Syntax ν , op

--------------------------------------------------------------------------------
-- Fold
--------------------------------------------------------------------------------

private variable 𝒞 : Type c
interp : 𝔽 -Alg[ 𝒞 ] → (ν → 𝒞) → Syntax ν → 𝒞
interp ϕ ρ (var x)        = ρ x
interp ϕ ρ (op (Oᵢ , k))  = ϕ (Oᵢ , λ i → interp ϕ ρ (k i))

--------------------------------------------------------------------------------
-- The base *dependent* functor for this type:
--------------------------------------------------------------------------------

data 𝔖𝔶𝔫𝔱𝔞𝔵 (A : Type a) (B : Type b) (P : B → Type c) : Type (a ℓ⊔ b ℓ⊔ c) where
  var  :  A                              → 𝔖𝔶𝔫𝔱𝔞𝔵 A B P
  op   :  (xs : ⟦ 𝔽 ⟧ B)
          (P⟨xs⟩ : ∀ i → P (xs .snd i))  → 𝔖𝔶𝔫𝔱𝔞𝔵 A B P

--------------------------------------------------------------------------------
-- Dependent eliminators for the syntax type
--------------------------------------------------------------------------------

⟪_⟫ : 𝔖𝔶𝔫𝔱𝔞𝔵 A (Syntax A) P → Syntax A
⟪ var x    ⟫ = var x
⟪ op xs _  ⟫ = op xs

DepAlg : (A : Type a) → (Syntax A → Type b) → Type (a ℓ⊔ b)
DepAlg A P = (xs : 𝔖𝔶𝔫𝔱𝔞𝔵 A (Syntax A) P) → P ⟪ xs ⟫

syntax DepAlg A (λ xs → P) = Ψ[ xs ⦂ Syntax A ] P

elim-s : (P : Syntax A → Type b) → DepAlg A P → (xs : Syntax A) → P xs
elim-s _ alg (var x)         = alg (var x)
elim-s P alg (op (Op , xs))  = alg (op (Op , xs) (λ i → elim-s P alg (xs i)))

--------------------------------------------------------------------------------
-- Bind
--------------------------------------------------------------------------------

module SyntaxBind where
  return : A → Syntax A
  return = var

  private variable
    ν′ : Type b

  infixl 4.5 _=<<_
  _=<<_ : (ν → Syntax ν′) → Syntax ν → Syntax ν′
  _=<<_ = interp op

  infixr 4.5 _>>=_
  _>>=_ : Syntax A → (A → Syntax B) → Syntax B
  xs >>= ρ = interp op ρ xs

  infixr 4.5 _>>_
  _>>_ : Syntax A → Syntax B → Syntax B
  xs >> ys = xs >>= λ _ → ys

  infixr 9 _<=<_
  _<=<_ : (B → Syntax C) → (A → Syntax B) → A → Syntax C
  (f <=< g) x = f =<< g x

  infixl 9 _>=>_
  _>=>_ : (A → Syntax B) → (B → Syntax C) → A → Syntax C
  _>=>_ = flip _<=<_

  infixr 4.5 _<$>_
  _<$>_ : (A → B) → Syntax A → Syntax B
  f <$> xs = xs >>= var ∘ f

  infixl 4.5 _<&>_
  _<&>_ : Syntax A → (A → B) → Syntax B
  xs <&> f = f <$> xs

  <$>-comp : (xs : Syntax A) → (f : A → B) → (g : B → C) → ((g ∘ f) <$> xs) ≡ (g <$> (f <$> xs))
  <$>-comp (var x)      f g   = refl
  <$>-comp (op (o , k)) f g i = op (o , λ a → <$>-comp (k a) f g i)

open SyntaxBind

--------------------------------------------------------------------------------
-- Properties about interps on syntax
--------------------------------------------------------------------------------

interp-id : 
  (xs : Syntax ν) → interp op var xs ≡ xs
interp-id (var x)        = refl
interp-id (op (Oᵢ , k))  = cong (op ∘ _,_ Oᵢ) (funExt λ i → interp-id (k i))

interp-fusion  :  (f : C → A) {g₁ : ⟦ 𝔽 ⟧ C → C} {g₂ : ⟦ 𝔽 ⟧ A → A} (c : B → C) →
                  (∀ xs → f (g₁ xs) ≡ g₂ (cmap f xs)) → 
               ∀  xs → f (interp g₁ c xs) ≡ interp g₂ (f ∘ c) xs
interp-fusion f            c p (var x)          = refl
interp-fusion f {g₂ = g₂}  c p (op (Oᵢ , xs) )  =
  p _ ⨾ cong g₂ (cong (Oᵢ ,_) (funExt λ x → interp-fusion f c p (xs x)))

interp-comp : ∀ (f : ⟦ 𝔽 ⟧ A → A) (k : B → A) (c : C → Syntax B) xs →
              interp f k (xs >>= c) ≡ interp f (interp f k ∘ c) xs
interp-comp f k c = interp-fusion (interp f k) c λ _ → refl

-- interp is a homomorphism
interp-homo : ∀ {ν C : Type} → (alg : 𝔽 -Alg[ C ]) → (ν → C)
            → ((Syntax ν , syntax-alg) ⟶ (C , alg))
interp-homo {ν = ν} alg k = interp alg k , funExt comm
  where
    comm :  (x : ⟦ 𝔽 ⟧ (Syntax ν)) → interp alg k (op x) ≡ alg (cmap (interp alg k) x)
    comm (o , xs) = refl

--------------------------------------------------------------------------------
-- Freeness of Syntax
--------------------------------------------------------------------------------

var-alg : (ν : Type) → (C : Type) → (alg : 𝔽 -Alg[ C ])
        → ((Syntax ν , syntax-alg {ν = ν}) ⟶ (C , alg)) → ν → C
var-alg ν C alg (h , _) x = h (var x)

open import Cubical.Foundations.Isomorphism using (isoToIsEquiv; Iso)

-- The homotopy freeness is essentially Theorem 5.4.7 in the HoTT book and studied
-- in detail in the following paper:
--
--   Steve Awodey, Nicola Gambino, and Kristina Sojakova. 2017. Homotopy-Initial
--   Algebras in Type Theory. J. ACM 63, 6, Article 51 (February 2017), 45 pages.
--   https://doi.org/10.1145/3006383
--
-- The following proof is generalised from the proof of homotopy initiality of natural
-- numbers in the cubical library (https://agda.github.io/cubical/Cubical.Data.Nat.Algebra.html).

syntax-is-free : ∀ {ν : Type} → (C : Type) → (alg : 𝔽 -Alg[ C ])
               → isEquiv (var-alg ν C alg)
syntax-is-free {ν} C alg = isoToIsEquiv i where
  i : Iso ((Syntax ν , syntax-alg {ν = ν}) ⟶ (C , alg)) (ν → C)
  i .fun = var-alg ν C alg
  i .inv k = interp-homo alg k
  i .rightInv k = refl
  i .leftInv (h , comm) = ΣPathP (h-path , comm-path) where
     h-var-fusion-ty : Syntax ν → Type
     h-var-fusion-ty x = interp alg (h ∘ var) x ≡ h x

     open import Cubical.Foundations.Prelude using (_∙∙_∙∙_)
     open import Cubical.Foundations.Path using (PathP≡doubleCompPathʳ)

     h-var-fusion-alg : DepAlg ν h-var-fusion-ty
     h-var-fusion-alg (var x) = refl
     h-var-fusion-alg (op oxs P⟨xs⟩) = refl ∙∙ p-IH ∙∙ sym (λ i → comm i oxs)  where
       p-IH : alg (oxs .fst , (λ a → interp alg (λ x → h (var x)) (oxs .snd a))) ≡ alg (cmap h oxs)
       p-IH = cong (λ xs' → alg (oxs .fst , xs')) (funExt (λ a → P⟨xs⟩ a))

     h-var-fusion : ∀ x → interp alg (h ∘ var) x ≡ h x
     h-var-fusion = elim-s h-var-fusion-ty h-var-fusion-alg

     h-path : interp alg (h ∘ var) ≡ h
     h-path = funExt h-var-fusion

     -- The key observation is that the h-path for the op case is defined by
     -- composing comm, p-IH, and (interp-homo alg (h ∘ var) .snd) (which is
     -- refl), so there is a trivial filler comm-path of the square formed by
     -- these four paths.
     squeezeSquare : ∀{a}{A : Type a}{w x y z : A} (p : w ≡ x) {q : x ≡ y} (r : z ≡ y)
                   → (P : w ≡ z) → (sq : P ≡ p ∙∙ q ∙∙ sym r) → I → I → A
     squeezeSquare p {q} r P sq i j = transport (sym (PathP≡doubleCompPathʳ p P q r)) sq i j


     comm-path : PathP (λ i → (λ xs → h-path i (op xs)) ≡ (λ xs → alg (cmap (h-path i) xs)))
                       (interp-homo alg (h ∘ var) .snd)
                       comm
     comm-path i j oxs = squeezeSquare (λ k → (interp-homo alg (h ∘ var) .snd) k oxs )
                                       (λ k → comm k oxs)
                                       (h-var-fusion (op oxs))
                                       (refl {x = h-var-fusion (op oxs)})
                                       j
                                       i

--------------------------------------------------------------------------------
-- Modality
--------------------------------------------------------------------------------

◇′ : ∀ {p} → (A → Type p) → Syntax A → Type p
◇′ P (var x) = P x
◇′ P (op (O , xs)) = ∃ i × ◇′ P (xs i)

□′ : ∀ {p} → (A → Type p) → Syntax A → Type p
□′ P (var x) = P x
□′ P (op (O , xs)) = ∀ i → □′ P (xs i)

□′->>=-□′ : ∀ {p q} (P : A → Type p) (Q : B → Type q) →
              (xs : Syntax A) (f : A → Syntax B) →
              (∀ x → P x → □′ Q (f x)) → □′ P xs → □′ Q (xs >>= f)
□′->>=-□′ P Q (var x) f t Pxs = t x Pxs
□′->>=-□′ P Q (op (Oᵢ , xs)) f t Pxs i = □′->>=-□′ P Q (xs i) f t (Pxs i)

◇′->>=-◇′ : ∀ {p q} (P : A → Type p) (Q : B → Type q) →
              (xs : Syntax A) (f : A → Syntax B) →
              (∀ x → P x → ◇′ Q (f x)) → ◇′ P xs → ◇′ Q (xs >>= f)
◇′->>=-◇′ P Q (var x) f t Pxs = t x Pxs
◇′->>=-◇′ P Q (op (Oᵢ , xs)) f t (i , Pxs) = i , ◇′->>=-◇′ P Q (xs i) f t Pxs

□′-fmap : ∀ {A : Type a} {P Q : A → Type p} (t : Syntax A) →
            (∀ (x : A) → P x → Q x) → (□′ P t → □′ Q t)
□′-fmap (var x) f p =  f x p
□′-fmap (op (o , k)) f p = λ a → □′-fmap (k a) f (p a)

◇′-fmap : ∀ {A : Type a} {P Q : A → Type p} (t : Syntax A) →
            (∀ (x : A) → P x → Q x) → (◇′ P t → ◇′ Q t)
◇′-fmap (var x) f p = f x p
◇′-fmap (op (o , k)) f (a , p) = a ,  ◇′-fmap (k a) f p

□′-shift : ∀ {A : Type a} {P : B → Type p} → (f : A → B) → (t : Syntax A) → □′ (P ∘ f) t → □′ P (f <$> t)
□′-shift f (var x) p = p
□′-shift f (op (o , k)) p a = □′-shift f (k a) (p a)

◇′-shift : ∀ {A : Type a} {P : B → Type p} → (f : A → B) → (t : Syntax A) → ◇′ (P ∘ f) t →  ◇′ P (f <$> t)
◇′-shift f (var x) p = p
◇′-shift f (op (o , k)) (a , p) = a , ◇′-shift f (k a) p

var-inj : Injective (Syntax.var {ν = A})
var-inj {x = x} {y} = cong λ { (var x) → x ; (op _) → x }

op-inj : Injective (Syntax.op {ν = A})
op-inj {x = x} {y} = cong λ { (var _) → x ; (op x) → x }

open import Cubical.Data.Sigma.Properties

opF-inj : isSet Op → (O : Op) → (xs ys : Arity O → Syntax A) → (op (O , xs) ⦂ Syntax A) ≡ op (O , ys) → xs ≡ ys
opF-inj set O xs ys p =
  Σ-contractFst (refl , λ _ → set _ _ _ _) .fst (PathPΣ (op-inj p))

isReturn : Syntax A → Bool
isReturn (var _) = true
isReturn (op _) = false

fmap-injective : (f : A → B) → Injective f → Injective (f <$>_)
fmap-injective f inj {var x} {var y} p = cong var (inj (var-inj p))
fmap-injective {A = A} {B = B} f inj {op (i , x)} {op (j , y)} p =
  let q = op-inj { x = i , _<$>_ f ∘ x } { y = j , _<$>_ f ∘ y } p
      h = cong fst q
  in cong (op ⦂ (⟦ 𝔽 ⟧ (Syntax _) → Syntax _))
    (cong₂ _,_ h
    (J (λ z zp → ∀ y → PathP (λ l → Arity (zp l) → Syntax B) (_<$>_ f ∘ x) (_<$>_ f ∘ y) → PathP (λ l → Arity (zp l) → Syntax A) x y)
        (λ y′ p′ → funExt λ k → fmap-injective f inj {x k} {y′ k} (cong (_$ k) p′)) h y (cong snd q)))
fmap-injective f inj {var x} {op y} p = absurd (true≢false (cong isReturn p))
fmap-injective f inj {op x} {var y} p = absurd (false≢true (cong isReturn p))

var≢op : ∀ {x : A} {O k} → var x ≢ op (O , k)
var≢op = true≢false ∘ cong isReturn

op≢var : ∀ {x : A} {O k} → op (O , k) ≢ var x
op≢var = false≢true ∘ cong isReturn

>>=-com-<$> : (f : A → Syntax B) (g : B → C) (xs : Syntax A) → (xs >>= λ x → g <$> f x) ≡ g <$> (xs >>= f)
>>=-com-<$> f g = elim-s _ λ { (var x) → refl ; (op (O , k) P⟨xs⟩) → cong (op ∘ _,_ O) (funExt P⟨xs⟩) }
