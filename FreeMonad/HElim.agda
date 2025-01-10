{-# OPTIONS --safe #-}

open import Prelude
open import FreeMonad.PackagedTheory
open import Signatures
import FreeMonad.Theory
open import Finite

module FreeMonad.HElim
  (T : FullTheory ℓzero)
  (findVar : FreeMonad.Theory.DiscreteVars (FullTheory.𝒯 T))
  (fin-arities : ∀ Oᵢ → ℰ (Signature.Arity (FullTheory.𝔽 T) Oᵢ))
  where

open FullTheory T

open module 𝕋 = FreeMonad.Theory ℓzero 𝔽

open import FreeMonad.Syntax 𝔽
open SyntaxBind using (_<$>_; <$>-comp) renaming (_>>=_ to _>>=ₛ_)
open import FreeMonad.Syntax.AsSignature 𝔽 hiding (_∈_ ; _∉_)
open import FreeMonad.Relation 𝔽 𝒯
open import Truth
open import Data.Sigma.Properties
open import Data.Lift.Properties

open Theory 𝒯

open Signature 𝔽 using (Arity)

disc-arities : ∀ Oᵢ → Discrete (Arity Oᵢ)
disc-arities Oᵢ = ℰ⇒Discrete (fin-arities Oᵢ)

setArity : ∀ Oᵢ → isSet (Arity Oᵢ)
setArity O = Discrete→isSet (disc-arities O)


infixr 5 _∈_ _∉_
_∈_ _∉_ : A → (B → A) → Type _
_∈_ = flip Fibre
x ∉ xs = ¬ (x ∈ xs)

ℰ⟨Index⟩ : (s : Syntax A) → ℰ (Index s)
ℰ⟨Index⟩ = elim-s _ λ { (var x) → ℰ⟨⊤⟩ ; (op (O , k) P⟨xs⟩) → ℰΣ (fin-arities O) P⟨xs⟩ }

∈? : Discrete A → (x : A) (s : Syntax B) (xs : Index s → A) → Dec ∥ x ∈ xs ∥
∈? discrete x s xs = ℰ⇒search (ℰ⟨Index⟩ s) λ i → discrete (xs i) x


record Provenance {A : Type a} (s t : Syntax A) : Type (ℓsuc a) where
  field
    Iₚ   : Type a
    I≟   : Discrete Iₚ
    sₚ   : Index s → Iₚ
    tₚ   : Index t → Iₚ
    eqvₚ : fill _ sₚ ~ₜ fill _ tₚ
    kₚ   : Iₚ → A
    s-k  : ∀ i → lookup s i ≡ kₚ (sₚ i)
    t-k  : ∀ i → lookup t i ≡ kₚ (tₚ i)

  ∈s? : ∀ v → Dec ∥ v ∈ sₚ ∥
  ∈s? v = ∈? I≟ v s sₚ

  ∈t? : ∀ v → Dec ∥ v ∈ tₚ ∥
  ∈t? v = ∈? I≟ v t tₚ


module DeriveEq {A : Type a} (i : Laws) (Γ : Eqns i .Γ) (k : Eqns i .ν Γ → Syntax A) where
  open Equation (eqn (Eqns i) Γ) renaming (lhs to lhs∙ ; rhs to rhs∙) using ()


  private module DisplayI where

    Iₚ : Type
    Iₚ = Σ[ v ⦂ Eqns i .ν Γ ] × Index (k v)

  Iₚ : Type a
  Iₚ = Lift (Σ[ v ⦂ Eqns i .ν Γ ] × Index (k v))

  I≟ : Discrete Iₚ
  I≟ = discreteLift (discreteΣ (findVar i Γ) λ x → disc-index disc-arities (k x))

  kₚ : Iₚ → A
  kₚ = uncurry (lookup ∘′ k) ∘ lower

  sₚ : >>=-ind lhs∙ k → Iₚ
  sₚ = lift ∘ map-Σ (lookup lhs∙) id ∘′ pull-shape k lhs∙

  tₚ : >>=-ind rhs∙ k → Iₚ
  tₚ = lift ∘ map-Σ (lookup rhs∙) id ∘′ pull-shape k rhs∙ 

  eqvₚ : fill _ sₚ ~ₜ fill _ tₚ
  eqvₚ = reflₜ (>>=⟦⟧ k _ lhs∙)
    ⟨ transₜ ⟩ eqₜ i Γ (λ v → fill _ (lift ∘ (v ,_)))
    ⟨ transₜ ⟩ reflₜ (sym (>>=⟦⟧ k _ rhs∙))

  s-k : ∀ i → lookup (lhs∙ >>=ₛ k) i ≡ kₚ (sₚ i)
  s-k i = sym (lookup-pull k lhs∙ i)

  t-k : ∀ i → lookup (rhs∙ >>=ₛ k) i ≡ kₚ (tₚ i)
  t-k i = sym (lookup-pull k rhs∙ i)


module DeriveCong {A : Type a} Oᵢ (kₗ kᵣ : Arity Oᵢ → Syntax A) (derive-at : ∀ i → Provenance (kₗ i) (kᵣ i)) where
  module _ (i : Arity Oᵢ) where module 𝒟 = Provenance (derive-at i)

  s t : Syntax A
  s = op (Oᵢ , kₗ)
  t = op (Oᵢ , kᵣ)

  Iₚ : Type _
  Iₚ = Σ[ i ⦂ Arity Oᵢ ] × 𝒟.Iₚ i

  I≟ : Discrete Iₚ
  I≟ = discreteΣ (disc-arities _) 𝒟.I≟

  sₚ : Index s → Iₚ
  sₚ (i , is) = i , 𝒟.sₚ i is

  tₚ : Index t → Iₚ
  tₚ (i , is) = i , 𝒟.tₚ i is

  eqvₚ : fill _ sₚ ~ₜ fill _ tₚ
  eqvₚ = congₜ Oᵢ _ _ λ i →
              reflₜ (sym (<$>-com-inv (_,_ i) (_ , 𝒟.sₚ i)))
    ⟨ transₜ ⟩ <$>-cong (_,_ i) (𝒟.eqvₚ i)
    ⟨ transₜ ⟩ reflₜ (<$>-com-inv (_,_ i) (_ , 𝒟.tₚ i))

  kₚ : Iₚ → A
  kₚ = uncurry 𝒟.kₚ

  s-k : ∀ i → lookup s i ≡ kₚ (sₚ i)
  s-k = uncurry 𝒟.s-k

  t-k : ∀ i → lookup t i ≡ kₚ (tₚ i)
  t-k = uncurry 𝒟.t-k


module DeriveTrans {A : Type a} (setA : isSet A) (s t u : Syntax A) (lhs′ : Provenance s u) (rhs′ : Provenance u t) where
  module rhs = Provenance rhs′
  module lhs = Provenance lhs′

  open import HITs.Pushout
  open import HITs.Pushout.Properties using (fin-disc-pushout)

  Iₚ : Type a
  Iₚ = Pushout {A = Index u} {B = lhs.Iₚ} {C = rhs.Iₚ} lhs.tₚ rhs.sₚ

  I≟ : Discrete Iₚ
  I≟ = fin-disc-pushout (ℰ⟨Index⟩ u) lhs.I≟ rhs.I≟

  kₚ : Iₚ → A
  kₚ (inl x)  = lhs.kₚ x
  kₚ (inr x)  = rhs.kₚ x
  kₚ (push i j) = (sym (lhs.t-k i) ⨾ rhs.s-k i) j
  kₚ (trunc x y p q i j) =
    setA (kₚ x) (kₚ y) (cong kₚ p) (cong kₚ q) i j

  sₚ : Index s → Iₚ
  sₚ = inl ∘ lhs.sₚ
  tₚ : Index t → Iₚ
  tₚ = inr ∘ rhs.tₚ

  eqvₚ : fill _ sₚ ~ₜ fill _ tₚ
  eqvₚ =       subst₂ _~ₜ_ (<$>-com-inv inl (_ , lhs.sₚ)) (<$>-com-inv inl (_ , lhs.tₚ)) (<$>-cong inl lhs.eqvₚ)
    ⟨ transₜ ⟩ reflₜ (cong (fill (shape u)) (funExt push))
    ⟨ transₜ ⟩ subst₂ _~ₜ_ (<$>-com-inv inr (_ , rhs.sₚ)) (<$>-com-inv inr (_ , rhs.tₚ)) (<$>-cong inr rhs.eqvₚ)

  s-k = lhs.s-k
  t-k = rhs.t-k

module DeriveRefl {A : Type a} (s : Syntax A) where
  Iₚ : Type a
  Iₚ = Lift (Index s)

  I≟ : Discrete Iₚ
  I≟ = discreteLift (disc-index disc-arities s)

  sₚ tₚ : Index s → Iₚ
  sₚ = lift
  tₚ = lift

  eqvₚ : fill _ sₚ ~ₜ fill _ tₚ
  eqvₚ = reflₜ refl

  kₚ : Iₚ → A
  kₚ = lookup s ∘ lower

  s-k t-k : ∀ i → lookup s i ≡ kₚ (lift i)
  s-k _ = refl
  t-k _ = refl


module DeriveSym {A : Type a} (s t : Syntax A) (derived-rev : Provenance t s) where
  module 𝓈 = Provenance derived-rev

  Iₚ = 𝓈.Iₚ
  I≟ = 𝓈.I≟
  sₚ = 𝓈.tₚ
  tₚ = 𝓈.sₚ
  eqvₚ = symₜ 𝓈.eqvₚ
  kₚ  = 𝓈.kₚ
  s-k = 𝓈.t-k
  t-k = 𝓈.s-k


module _ (setA : isSet A) where
  open Theory 𝒯
  open import FinitenessConditions using (SplitQuotientedChoice⇒Choice)

  derive : (s t : Syntax A) → s ~ₜ t → ∥ Provenance s t ∥
  derive _ _ (eqₜ i Γ k)        = ∣ record { DeriveEq i Γ k } ∣
  derive s t (reflₜ p)          = ∣ subst (Provenance s) p (record { DeriveRefl s }) ∣
  derive s t (symₜ p)           = ∥map∥ (λ p′ → record { DeriveSym s t p′ }) (derive _ _ p)
  derive s t (transₜ p q)       = ∥liftA2∥ (λ lhs rhs → record { DeriveTrans setA s t _ lhs rhs }) (derive _ _ p) (derive _ _ q)
  derive s t (truncₜ p q i)     = squash (derive s t p) (derive s t q) i
  derive _ _ (congₜ Oᵢ kₗ kᵣ x) =
    ∥map∥ (λ d → record { DeriveCong Oᵢ kₗ kᵣ d })
          (SplitQuotientedChoice⇒Choice (setArity Oᵢ) (finiteArity Oᵢ) λ i → derive (kₗ i) (kᵣ i) (x i))

private
  variable
    s : Syntax A
    t : Syntax B


import FreeMonad.Quotiented T as OnTerm

open OnTerm
  using (syntactic-bind; join; >>=-join-eq; >>=-join-comm; <$>-comm)
  renaming (_<$>_ to _<$>ₜ_ ; _>>=_ to _>>=ₜ_ ; return to returnₜ)

module _ {A : Type a} (ϕ : A → Ω c)
  where
  ϕ? : A → A × Ω c
  ϕ? x = x , ϕ x

  ϕT : A → A × Ω c
  ϕT x = x , True

  module _ (setA : isSet A) where

    -- This can be cleaned up a lot: since we switched to the container rep, a lot
    -- of the proofs here should trivialise if stated carefully.
    module _ (setB : isSet B)
            (f g : A → B) (k : (x : A) → ProofOf (ϕ x) → f x ≡ g x)
            (s : Syntax A)          
            (pr : ϕ? <$> s ~ₜ ϕT <$> s)
            where
      𝒢-elim′ : f <$> s ~ₜ g <$> s

      𝒢-elim′ = ∥rec∥ truncₜ Helper.theorem (derive (isSetΣ setA (λ _ → isSetΩ)) (ϕ? <$> s) (ϕT <$> s) pr)
        where
        module Helper
          (d : Provenance (ϕ? <$> s) (ϕT <$> s)) where
          open Provenance d

          k′ : Iₚ → B
          k′ i =  let v = kₚ i .fst in if  does (∈s? i) then f v else g v
          ∈sₚ⇒f : (i : Index (ϕ? <$> s)) → k′ (sₚ i) ≡ f (fst (kₚ (sₚ i)))
          ∈sₚ⇒f i with ∈s? (sₚ i)
          ... | yes _ = refl
          ... | no ¬p = absurd (¬p ∣ i , refl ∣)

          ts₁ : f <$> s ≡ k′ <$> fill _ sₚ
          ts₁ =
            f <$> s                                ≡⟨ <$>-comp s _ _ ⟩
            f ∘ fst <$> ϕ? <$> s                   ≡˘⟨ cong (f ∘ fst <$>_) (Indexed .leftInv (ϕ? <$> s)) ⟩
            f ∘ fst <$> fill _ (lookup (ϕ? <$> s)) ≡⟨ cong ((f ∘ fst <$>_) ∘ fill _) (funExt s-k) ⟩
            f ∘ fst <$> fill _ (kₚ ∘ sₚ)           ≡⟨ <$>-com-inv (f ∘ fst) _ ⟩
            fill _ (f ∘ fst ∘ kₚ ∘ sₚ)             ≡˘⟨ cong (fill _) (funExt ∈sₚ⇒f) ⟩
            fill _ (k′ ∘ sₚ)                       ≡˘⟨ <$>-com-inv k′ _ ⟩
            k′ <$> fill _ sₚ ∎
          ∈tₚ⇒g : (i : Index (ϕT <$> s)) → k′ (tₚ i) ≡ g (fst (kₚ (tₚ i)))
          ∈tₚ⇒g i with ∈s? (tₚ i)
          ... | no _ = refl
          ... | yes j,q = flip (∥rec∥ (setB _ _)) j,q (λ { (j , q) →
              k (kₚ (tₚ i) .fst) $ extract $
                ϕ (kₚ (tₚ i) .fst)            ≡˘⟨ cong (ϕ ∘ fst) (s-k j ⨾ cong kₚ q) ⟩
                ϕ (lookup (ϕ? <$> s)  j .fst) ≡⟨ cong (ϕ ∘ fst) (<$>-lookup ϕ? s j) ⨾ cong snd (sym (<$>-lookup ϕ? s j)) ⟩ 
                lookup (ϕ? <$> s) j .snd      ≡⟨ cong snd (s-k j ⨾ cong kₚ q ⨾ sym (t-k i)) ⟩
                lookup (ϕT <$> s) i .snd      ≡⟨ cong snd (<$>-lookup ϕT s i) ⟩
                True ∎
              })

          ts₂ : g <$> s ≡ k′ <$> fill _ tₚ
          ts₂ = 
            g <$> s                                ≡⟨ <$>-comp s _ _ ⟩
            g ∘ fst <$> ϕT <$> s                   ≡˘⟨ cong (g ∘ fst <$>_) (Indexed .leftInv (ϕT <$> s)) ⟩
            g ∘ fst <$> fill _ (lookup (ϕT <$> s)) ≡⟨ cong ((g ∘ fst <$>_) ∘ fill _) (funExt t-k) ⟩
            g ∘ fst <$> fill _ (kₚ ∘ tₚ)           ≡⟨ <$>-com-inv (g ∘ fst) _ ⟩
            fill _ (g ∘ fst ∘ kₚ ∘ tₚ)             ≡˘⟨ cong (fill _) (funExt ∈tₚ⇒g)  ⟩
            fill _ (k′ ∘ tₚ)                       ≡˘⟨ <$>-com-inv k′ _ ⟩
            k′ <$> fill _ tₚ ∎

          theorem : f <$> s ~ₜ g <$> s
          theorem = reflₜ ts₁ ⟨ transₜ ⟩ <$>-cong k′ eqvₚ ⟨ transₜ ⟩ reflₜ (sym ts₂)

    module _ {B : Type b}
            (f g : A → Term B) (k : (x : A) → ProofOf (ϕ x) → f x ≡ g x) (p : Term A)
            (path : ϕ? <$>ₜ p ≡ ϕT <$>ₜ p)
            where
      𝒢-elim″ : p >>=ₜ f ≡ p >>=ₜ g
      𝒢-elim″ = elimProp/-with {D = λ p → (ϕ? <$>ₜ p) ≡ (ϕT <$>ₜ p)} (λ p _ → squash/ (p >>=ₜ f) (p >>=ₜ g)) go p path
        where
        module _ (pₛ : Syntax A) (path : ϕ? <$>ₜ [ pₛ ] ≡ ϕT <$>ₜ [ pₛ ]) where
          d : ϕ? <$> pₛ ~ₜ ϕT <$> pₛ
          d = ~ₜ-effective (ϕ? <$>  pₛ) (ϕT <$> pₛ) (sym (<$>-comm pₛ ϕ?) ⨾ path ⨾ <$>-comm pₛ ϕT)

          h : ([ f <$> pₛ ] ⦂ Term _) ≡ [ g <$> pₛ ]
          h = eq/ _ _ (𝒢-elim′ squash/ f g k pₛ d)

          go : [ pₛ ] >>=ₜ f ≡ [ pₛ ] >>=ₜ g
          go =
            [ pₛ ] >>=ₜ f        ≡⟨ >>=-join-comm pₛ f ⟩
            [ f <$> pₛ ] >>=ₜ id ≡⟨ cong (_>>=ₜ id) h ⟩
            [ g <$> pₛ ] >>=ₜ id ≡˘⟨ >>=-join-comm pₛ g ⟩
            [ pₛ ] >>=ₜ g ∎

𝒢-elim  :  (ϕ : A → Ω c)
        →  (f g : A → Term B)
        →  (k : (x : A) → ProofOf (ϕ x) → f x ≡ g x)
        →  (p : Term A)
        →  (ϕ? ϕ <$>ₜ p ≡ ϕT ϕ <$>ₜ p)
        →  (p >>=ₜ f) ≡ (p >>=ₜ g)
𝒢-elim ϕ f g k p path =
  let h = 𝒢-elim″
             (∥rec∥₂ isSetΩ ϕ)
             squash₂
             (∥rec∥₂ squash/ f)
             (∥rec∥₂ squash/ g)
             (∥elim∥₂ (λ _ → isSet→ (isProp→isSet (squash/ _ _))) k)
             (∣_∣₂ <$>ₜ p)
             ( OnTerm.<$>-comp _ _ p
             ⨾ sym (OnTerm.<$>-comp (map₁ ∣_∣₂) (ϕ? ϕ) p)
             ⨾ cong (map₁ ∣_∣₂ <$>ₜ_) path
             ⨾ OnTerm.<$>-comp (map₁ ∣_∣₂) (ϕT ϕ) p
             ⨾ sym (OnTerm.<$>-comp _ _ p))
  in sym (OnTerm.assoc p (OnTerm.return ∘ ∣_∣₂) (∥rec∥₂ squash/ f)) ⨾ h ⨾ OnTerm.assoc p (OnTerm.return ∘ ∣_∣₂) (∥rec∥₂ squash/ g)
