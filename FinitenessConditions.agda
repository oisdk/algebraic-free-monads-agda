{-# OPTIONS --safe #-}

module FinitenessConditions where

open import Prelude
open import Axiom


module _ {A : Type a} {B : Type b} where
  Pointwise : (B → B → Type c) → (A → B) → (A → B) → Type _
  Pointwise R f g = ∀ x → [ f x ] ≡ ([ g x ] ⦂ B / R)
private variable _~_ : B → B → Type c
private variable R : B → B → Type c
dist : (A → B) / Pointwise R → (A → B / R)
dist = rec/ (isSetΠ λ _ → squash/) (λ f → [_] ∘ f) (λ _ _ → funExt)
quot-pre : (A : Type a) → Typeω
quot-pre A = ∀ {b c} (B : Type b) (R : B → B → Type c) →
  Σ[  trav ⦂ ((A → B / R) → (A → B) / Pointwise R) ] ×
    (trav ∘ dist ≡ id) × (dist ∘ trav ≡ id)
inj-dist : Injective (dist {A = A} {B = B} {R = _~_})
inj-dist {x = x} {y = y} =
  elimProp2/
    {P = λ x y → dist x ≡ dist y → x ≡ y}
    (λ _ _ → isProp→ (squash/ _ _))
    (λ x y p → eq/ x y λ z → cong (_$ z) p)
    x y

record SplitQuotientedChoiceAt (A : Type a) (B : Type b) (_~_ : B → B → Type c) : Type (a ℓ⊔ b ℓ⊔ c) where
  no-eta-equality
  -- In reality, there is no need for this to be split surjective. If it's just
  -- surjective, we can derive split (as is proven in quotientedChoiceSplit
  -- below). However, that definition slows down Agda so much it's unusable, so
  -- we go with this one instead.
  field
    undistrib : SplitSurjective (dist {A = A} {B = B} {R = _~_})

  trav : (A → B / _~_) → (A → B) / Pointwise _~_
  trav f = undistrib f .fst

  dist∘trav : (f : A → B / _~_) (x : A) → dist (trav f) x ≡ f x
  dist∘trav f x = cong (_$ x) (undistrib f .snd)

  un-trav : (f : A → B) → trav ([_] ∘ f) ≡ [ f ]
  un-trav f =
    elimProp/
      {P = λ xs → xs ≡ trav ([_] ∘ f) → xs ≡ [ f ]}
      (λ _ → isProp→ (squash/ _ _))
      (λ g p → eq/ _ _ λ x → cong (λ h → dist h x) p ⨾ dist∘trav ([_] ∘ f) x)
      (trav ([_] ∘ f)) refl

  trav∘dist : (x : (A → B) / Pointwise _~_)
            → trav (dist x) ≡ x
  trav∘dist = elimProp/ (λ _ → squash/ _ _) un-trav

  comm-quot : (A → B / _~_) ⇔ (A → B) / Pointwise _~_
  comm-quot .fun = trav
  comm-quot .inv = dist
  comm-quot .rightInv = trav∘dist
  comm-quot .leftInv x = funExt (dist∘trav x)

  choose~canonical : (k : A → B / _~_) → ∥ ∃ k′ × [_] ∘ k′ ≡ k ∥
  choose~canonical k =
    elimProp/ {P = λ k′ → dist k′ ≡ k → ∥ ∃ k′ × [_] ∘ k′ ≡ k ∥}
      (λ _ → isProp→ squash)
      (λ k′ r → ∣ k′ , r ∣)
      (trav k)
      (undistrib k .snd)

  elim~canonical : (P : (A → B / _~_) → Type c)
                 → (∀ k → isProp (P k))
                 → (∀ k′ → P ([_] ∘ k′))
                 → ∀ k → P k
  elim~canonical P prop r k = ∥rec∥ (prop _) (λ { (k′ , p) → subst P p (r k′)  }) (choose~canonical k)

SplitQuotientedChoice : Type a → ∀ b c → Type _
SplitQuotientedChoice A b c =
  ∀ {B : Type b} {_~_ : B → B → Type c} → SplitQuotientedChoiceAt A B _~_

SplitQuotientedChoiceω : Type a → Typeω
SplitQuotientedChoiceω A = ∀ {b c} → SplitQuotientedChoice A b c

open SplitQuotientedChoiceAt

-- This property actually implies the property above. However, as mentioned
-- above, using it directly slows down Agda too much so we don't bother.

record QuotientedChoiceAt (A : Type a) (B : Type b) (_~_ : B → B → Type c) : Type (a ℓ⊔ b ℓ⊔ c) where
  field ∥undistrib∥ : Surjective (dist {A = A} {B = B} {R = _~_})

  splitQuotientedChoiceAt : SplitQuotientedChoiceAt A B _~_
  splitQuotientedChoiceAt .undistrib f = 
    ∥rec∥
      (λ  x y → Σ≡Prop (λ _ → isSet→ squash/ _ _) (inj-dist (x .snd ⨾ sym (y .snd))))
      id
      (∥undistrib∥ f)


open QuotientedChoiceAt public

[_]-pw : (A → B) → (A → B / R)
[ f ]-pw x = [ f x ]

-- The following is an equivalent formulation of QuotientedChoiceAt, and it is
-- very close to "projective objects" in category theory, thus "quotiented projective".
QProjectiveAt : (A : Type a) → (B : Type b) → (R : B → B → Type c) → Type _
QProjectiveAt A B _~_ = Surjective (([_] ∘_) ⦂ ((A → B) → (A → B / _~_)))

open import Cubical.Foundations.Univalence using (hPropExt)

QProjective-QComm-equiv : QuotientedChoiceAt A B _~_ ≡ QProjectiveAt A B _~_
QProjective-QComm-equiv = hPropExt qc-prop (isPropΠ (λ _ → squash)) projective-fwd projective-bwd where
  qc-prop : isProp (QuotientedChoiceAt A B _~_)
  qc-prop x y i =  record { ∥undistrib∥ = isPropΠ (λ _ → squash) (∥undistrib∥ x) (∥undistrib∥ y) i}

  projective-fwd : ∀ {A : Type a} {B : Type b} {_~_ : B → B → Type c}
                  → QuotientedChoiceAt A B _~_ → QProjectiveAt A B _~_
  projective-fwd {A = A} {B = B} {_~_ = _~_} q f =  ∥bind∥ fwd (∥undistrib∥ q f) where
    fwd : Fibre dist f → ∥ Fibre (([_] ∘_) ⦂ ((A → B) → (A → B / _~_))) f ∥
    fwd (g , e) = elimProp/-with {D = λ g → dist g ≡ f} (λ _ _ → squash)
                            (λ h e' → ∣ h , e' ∣)
                            g
                            e

  projective-bwd : ∀ {A : Type a} {B : Type b} {_~_ : B → B → Type c}
                → QProjectiveAt A B _~_ → QuotientedChoiceAt A B _~_
  projective-bwd {A = A} {B = B} {_~_ = _~_} q = record { ∥undistrib∥ = λ f →  ∥bind∥ (bwd f) (q f) } where
    bwd : ∀ f → Fibre (([_] ∘_) ⦂ ((A → B) → (A → B / _~_))) f → ∥ Fibre dist f ∥
    bwd f (g , e) = ∣ [ g ] , e ∣


QuotientedChoice : Type a → ∀ b c → Type _
QuotientedChoice A b c = ∀ {B : Type b} {_~_ : B → B → Type c} → QuotientedChoiceAt A B _~_

isPropQuotientedChoice : isProp (QuotientedChoice A b c)
isPropQuotientedChoice x y i .∥undistrib∥ z = squash (x .∥undistrib∥ z) (y .∥undistrib∥ z) i

QuotientedChoiceω : Type a → Typeω
QuotientedChoiceω A = ∀ {b c} → QuotientedChoice A b c

quotientedChoiceSplit : QuotientedChoice A b c → SplitQuotientedChoice A b c
quotientedChoiceSplit fp = splitQuotientedChoiceAt fp

Choice⇒QuotientedChoice : Choice A (b ℓ⊔ c) → QuotientedChoice A b c
Choice⇒QuotientedChoice aoc .∥undistrib∥ f =
  ∥rec∥ squash (λ h → ∣ [ (λ x → h x .fst) ] , (funExt λ x → snd (h x)) ∣) (aoc (λ x′ → []-surj (f x′)))

module _ where
  open import HITs.SetTruncation

  AOC⇒QuotientedChoice : AOC a a → ({A : Type a} → QuotientedChoice A a a)
  AOC⇒QuotientedChoice aoc .∥undistrib∥ f =
    let ac = aoc squash₂ λ x′ →  []-surj (∥rec∥₂ squash/ f x′) 
    in ∥rec∥ squash (λ h → ∣ [ (λ x → h ∣ x ∣₂ .fst) ] , (funExt λ x → h ∣ x ∣₂ .snd ) ∣) ac


open import Data.Sigma.Subset
open import Data.Sigma.Properties

module _ {A : Type a} (set : isSet A) (qc : SplitQuotientedChoice A (a ℓ⊔ b) a) where

  SplitQuotientedChoice⇒Choice : Choice A b
  SplitQuotientedChoice⇒Choice {B = 𝒰} f = ∥map∥ (Π⇔Σ set .inv) combined-sigma-trunc
    where
    f/ : A → Subset/ A 𝒰 
    f/ x = subset-quot (x , f x)

    fst/ : Subset/ A 𝒰 → A
    fst/ = rec/ set fst λ _ _ → id

    f⁻ : Fibre dist f/
    f⁻ = qc .undistrib f/

    fst∘f : ∀ x → fst/ (f/ x) ≡ x
    fst∘f x = 
      ∥elim∥
        { P = λ f·x → fst/ (subset-quot (x , f·x)) ≡ x }
        (λ _ → set _ _)
        (λ _ → refl)
        (f x)

    combined-sigma-trunc : ∥ Π⟨Σ⟩ A 𝒰 ∥
    combined-sigma-trunc =
      elimProp/
        { P = λ f⁻ → dist f⁻ ≡ f/ → ∥ Π⟨Σ⟩ A 𝒰 ∥ }
        (λ _ → isProp→ squash)
        (λ f⁻ f⁻Π → ∣ f⁻ , (λ x → cong (fst/ ∘ (_$ x)) f⁻Π ⨾ fst∘f x) ∣)
        (f⁻ .fst) (f⁻ .snd)

QuotientedChoice⇔SplitQuotientedChoice : QuotientedChoice A b c ⇔ SplitQuotientedChoice A b c
QuotientedChoice⇔SplitQuotientedChoice .fun = quotientedChoiceSplit
QuotientedChoice⇔SplitQuotientedChoice .inv qc .∥undistrib∥ y = ∣ qc .undistrib y ∣
QuotientedChoice⇔SplitQuotientedChoice .rightInv qc i .undistrib = qc .undistrib
QuotientedChoice⇔SplitQuotientedChoice .leftInv  _ = isPropQuotientedChoice _ _

QuotientedChoice⇔Choice : AOC a a ↔ ({A : Type a} → QuotientedChoice A a a)
QuotientedChoice⇔Choice .fst = AOC⇒QuotientedChoice
QuotientedChoice⇔Choice .snd qc set = SplitQuotientedChoice⇒Choice set (quotientedChoiceSplit qc)
-- QuotientedChoice⇔Choice .rightInv _ = {!!} -- isPropQuotientedChoice _ _
-- QuotientedChoice⇔Choice .leftInv  _ = {!!} -- isProp→ isPropChoice _ _

quotientedChoice⊥ : SplitQuotientedChoice ⊥ b c
quotientedChoice⊥ .undistrib y = [ absurd ] , (funExt λ ())

module UnitInst where
  unitTrav : B / _~_ → (⊤ → B) / Pointwise _~_
  unitTrav = rec/ squash/ ([_] ∘ const) (λ x y x~y → eq/ _ _ λ i → eq/ x y x~y)

  quotientedChoice⊤ : SplitQuotientedChoice ⊤ b c
  quotientedChoice⊤ .undistrib f = unitTrav (f tt) , funExt (λ x →
    elimProp/
      {P = λ ftt → ftt ≡ f tt → dist (unitTrav ftt) tt ≡ f tt }
      (λ _ → isProp→ (squash/ _ _))
      (λ ftt p → p)
      (f tt)
      refl)

open UnitInst using (quotientedChoice⊤) public


module BoolInst where
  boolTrav : B / _~_ → B / _~_ → (Bool → B) / Pointwise _~_
  boolTrav =
    rec2/
      squash/
      (λ f t → [ bool f t ])
      (λ x y z p → eq/ _ _ λ { false → eq/ _ _ p ; true → refl })
      (λ x y z p → eq/ _ _ λ { false → refl ; true → eq/ _ _ p })

  quotientedChoiceBool : SplitQuotientedChoice Bool b c
  quotientedChoiceBool .undistrib f = boolTrav (f false) (f true) , funExt (λ x →
    elimProp2/
      {P = λ l r → l ≡ f false → r ≡ f true → dist (boolTrav l r) x ≡ f x}
      (λ _ _ → isProp→ (isProp→ (squash/ _ _)))
      (λ fl tr fp tp → bool {P = λ x → [ bool′ fl tr x ] ≡ f x } fp tp x)
      (f false)
      (f true)
      refl
      refl)

open BoolInst using (quotientedChoiceBool) public

module ProdInst
  (finLhs : SplitQuotientedChoiceω A)
  (finRhs : SplitQuotientedChoiceω B)
  where

  lemma : (f g : A → B → C) → Pointwise (Pointwise _~_) f g → [ uncurry f ] ≡ [ uncurry g ]
  lemma {C = C} {_~_ = _~_} f g p = eq/ {R = Pointwise _~_} _ _ λ { (x , y) → effective/ (λ x y → isPropΠ λ _ → squash/ _ _) er _ _ (p x) y }
    where
    er : isEquivRel (λ f g → ∀ x → [ f x ] ≡ [ g x ])
    er .isEquivRel.reflexive a x = refl
    er .isEquivRel.symmetric a b p x = sym (p x)
    er .isEquivRel.transitive a b c p q x = p x ⨾ q x

  prodTrav : {C : Type c} {_~_ : C → C → Type b} → (A × B → C / _~_) → (A × B → C) / Pointwise _~_
  prodTrav {C = C} {_~_ = _~_} f = rec/ squash/ ([_] ∘ uncurry) lemma (fst (undistrib finLhs (λ x → fst (undistrib finRhs (curry f x)))))

  quotientedChoiceProd : SplitQuotientedChoiceω (A × B)
  quotientedChoiceProd {B = C} {_~_ = _~_} .undistrib f = prodTrav f ,
      funExt 
        (λ { (x , y) →
             elimProp/
               {P = λ r → r ≡ unLhs .fst → dist (rec/ squash/ ([_] ∘ uncurry) lemma r) (x , y) ≡ f (x , y)  }
               (λ _ → isProp→ (squash/ _ _))
               (λ h q →
                 dist [ uncurry h ] (x , y) ≡⟨⟩
                 [ h x y ] ≡⟨ cong (λ e → dist (e x) y) (cong dist q ⨾ unLhs .snd) ⟩
                 dist (unRhs x .fst) y ≡⟨ cong (_$ y) (unRhs x .snd) ⟩
                 f (x , y) ∎
                 )
               _ refl
          })
    where
    unRhs : (x : A) → Fibre dist (curry f x)
    unRhs x = undistrib finRhs (curry f x)

    unLhs : Fibre dist (λ x → fst (unRhs x))
    unLhs = undistrib finLhs (λ x → fst (unRhs x))
open ProdInst using (quotientedChoiceProd) public

module SumInst
  (finLhs : SplitQuotientedChoice A b c)
  (finRhs : SplitQuotientedChoice B b c)
  where
  sumTrav : (A → C) / Pointwise _~_ → (B → C) / Pointwise _~_ → (A ⊎ B → C) / Pointwise _~_
  sumTrav =
    rec2/
      squash/
      (λ f g → [ either f g ])
      (λ f g h p → eq/ _ _ λ { (inl x) → p x ; (inr x) → refl} )
      (λ f g h p → eq/ _ _ λ { (inl x) → refl ; (inr x) → p x })

  quotientedChoiceSum : SplitQuotientedChoice (A ⊎ B) b c
  quotientedChoiceSum .undistrib f = sumTrav 
      (fst (undistrib finLhs (f ∘ inl))) (fst (undistrib finRhs (f ∘ inr))) ,
    funExt (λ t →
        elimProp2/
          {P = λ x y → x ≡ fst (undistrib finLhs (f ∘ inl)) → y ≡ fst (undistrib finRhs (f ∘ inr)) →  dist (sumTrav x y) t ≡ f t }
          (λ _ _ → isProp→ (isProp→ (squash/ _ _)))
          (λ g h p q →
            let lhs = cong dist p ⨾ undistrib finLhs (f ∘ inl) .snd
                rhs = cong dist q ⨾ undistrib finRhs (f ∘ inr) .snd
            in either {C = λ t → dist [ either g h ] t ≡ f t} (λ x → cong (_$ x) lhs) (λ x → cong (_$ x) rhs) t )
          _ _ refl refl)
open SumInst using (quotientedChoiceSum) public

module LiftInst
  (finPres : SplitQuotientedChoice A b c)
  {ℓ : Level}
  where

  liftTrav : {B : Type b} {_~_ : B → B → Type c} → (Lift {ℓ₂ = ℓ} A → B / _~_) → (Lift {ℓ₂ = ℓ} A → B) / Pointwise _~_
  liftTrav y = rec/ squash/ (λ f → [ f ∘ lower ]) (λ f g p → eq/ _ _ λ x →  p (lower x)  ) (undistrib finPres (y ∘ lift) .fst)

  open import Data.Lift.Properties

  quotientedChoiceLift : SplitQuotientedChoice (Lift {ℓ₂ = ℓ} A) b c
  quotientedChoiceLift .undistrib y = liftTrav y ,
    elimProp/
      {P = λ y′ → y′ ≡ (undistrib finPres (λ x → y (lift x)) .fst) → dist (rec/ squash/ (λ f → [ f ∘ lower ] ) _ y′ ) ≡ y}
      (λ _ → isProp→ (isSetΠ (λ _ → squash/ ) _ _ ) )
      (λ f p → funExt (λ { (lift h) → (cong (λ e → dist e h) p) ⨾ cong (_$ h) (undistrib finPres (y ∘ lift) .snd) } ))
      _
      refl

open LiftInst using (quotientedChoiceLift) public

-- Instance for circle, just to show that being SplitQuotientedChoice is not the
-- same as being equivalent to some Fin.
module CircInst where
  open import Cubical.HITs.S1

  circTrav : B / _~_ → (S¹ → B) / Pointwise _~_
  circTrav = rec/ squash/ ([_] ∘ const) (λ x y x~y → eq/ _ _ λ i → eq/ x y x~y)

  quotientedChoiceS : SplitQuotientedChoice S¹ b c
  quotientedChoiceS .undistrib f = circTrav (f base) ,
    funExt (toPropElim (λ _ → squash/ _ _)
    (elimProp/
      {P = λ ftt → ftt ≡ f base → dist (circTrav ftt) base ≡ f base }
      (λ _ → isProp→ (squash/ _ _))
      (λ ftt p → p)
      (f base)
      refl))
