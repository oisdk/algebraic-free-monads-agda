{-# OPTIONS --safe --lossy-unification #-}

module Effects.NonDet where

open import Prelude hiding ([_]) renaming (tt to ⟨⟩)
open import Signatures
open import Data.Vec
open import Data.Vec.SetQuotients
open import FinitenessConditions
open import FreeMonad.PackagedTheory

module NonDet where
  data Op : Type 
  data Op where
    `fail  : Op
    `<|>   : Op
  Arity : Op → Type
  Arity `fail  = ⊥
  Arity `<|>   = Bool

open NonDet

ℕ𝔻 : Signature
ℕ𝔻 = Op ◁ Arity

private module RawOperators where
  _<|>_ : A → A → ⟦ ℕ𝔻 ⟧ A
  x <|> y =
    `<|> , λ i → if i then y else x

  fail : ⟦ ℕ𝔻 ⟧ A
  fail = `fail , λ ()

module _ {A : Type} where
  list-int : ℕ𝔻 -Alg[ List A ]
  list-int (`<|>   , k) = k false ++ k true
  list-int (`fail  , k) = []

any-int : ℕ𝔻 -Alg[ Bool ]
any-int (`fail  , k) = false
any-int (`<|>   , k) = k false || k true
all-int : ℕ𝔻 -Alg[ Bool ]
all-int (`fail  , k) = true
all-int (`<|>   , k) = k false && k true
  

open import FreeMonad.Theory

module Synt where
  open import FreeMonad.Syntax public hiding (Op⟦_⟧)
  open import FreeMonad.Syntax ℕ𝔻 using (Op⟦_⟧)

  norm-alg : ℕ𝔻 -Alg[ Syntax ℕ𝔻 A ]
  norm-alg (`fail , k) = op (`fail , absurd)
  norm-alg (`<|>  , k) = op (`<|>  , bool (k false) (k true))

  norm : Syntax ℕ𝔻 A → Syntax ℕ𝔻 A
  norm = interp ℕ𝔻 norm-alg var


  module BindParameterised where
    return : A → Syntax ℕ𝔻 A
    return = var
    _>>=_ : Syntax ℕ𝔻 A → (A → Syntax ℕ𝔻 B) → Syntax ℕ𝔻 B
    var x       >>= ρ = ρ x
    op (o , k)  >>= ρ = op (o , λ i → k i >>= ρ)

  open SyntaxBind ℕ𝔻


  infixl 6 _<|>_
  _<|>_ :  Syntax ℕ𝔻 A →
           Syntax ℕ𝔻 A →
           Syntax ℕ𝔻 A
  x <|> y = op (`<|> , λ i → if i then y else x)
  fail : Syntax ℕ𝔻 A
  fail = op (`fail , absurd)
  module OddsExample where
    open import Data.List.Syntax
    open import Agda.Builtin.Nat using (_+_; _*_; _==_)

    guard : Bool → Syntax ℕ𝔻 ⊤
    guard c = if c then return ⟨⟩ else fail
    up-to : ℕ → Syntax ℕ𝔻 ℕ
    up-to zero     = fail
    up-to (suc n)  = up-to n <|> return n
    module Desugared where
      odds : ℕ → Syntax ℕ𝔻 ℕ
      odds n = up-to n >>= λ m → guard (odd m) >>= λ _ → return m
    odds : ℕ → Syntax ℕ𝔻 ℕ
    odds n = do m ← up-to n
                guard (odd m)
                return m
  one-of : List A → Syntax ℕ𝔻 A
  one-of []        = fail
  one-of (x ∷ xs)  = return x <|> one-of xs

  open Law public
  open Equation public

  module AssocLaw where
    module Literals where
      assoc : Equation ℕ𝔻 (Fin 3)
      assoc = (var 0 <|> var 1) <|> var 2 ≐ var 0 <|> (var 1 <|> var 2)
    assoc : Equation ℕ𝔻 (Fin 3)
    assoc = ∀ⁿ λ x y z → (x <|> y) <|> z ≐ x <|> (y <|> z)
  data Laws : Type where idˡ assoc comm idem : Laws

  Eqns : Laws → Law 0 ℕ𝔻
  Eqns idˡ .Γ = ⊤
  Eqns idˡ .ν _ = Fin 1
  Eqns assoc .Γ  = ⊤
  Eqns assoc .ν _ = Fin 3
  Eqns comm .Γ  = ⊤
  Eqns comm .ν _ = Fin 2
  Eqns idem .Γ = ⊤
  Eqns idem .ν _ = Fin 1
  Eqns idˡ    .eqn _ = ∀ⁿ λ xs        → fail <|> xs         ≐ xs
  Eqns assoc  .eqn _ = ∀ⁿ λ xs ys zs  → (xs <|> ys) <|> zs  ≐ xs <|> (ys <|> zs)
  Eqns comm   .eqn _ = ∀ⁿ λ xs ys     → xs <|> ys           ≐ ys <|> xs
  Eqns idem   .eqn _ = ∀ⁿ λ xs        → xs <|> xs           ≐ xs

open Synt using (module AssocLaw; module OddsExample) public

NonDetLaws : Theory _ _
NonDetLaws = record { Synt }

nonDetFiniteVars : FiniteVars NonDetLaws
nonDetFiniteVars Synt.idˡ _ = fin-SplitQuotientedChoice
nonDetFiniteVars Synt.assoc _ = fin-SplitQuotientedChoice
nonDetFiniteVars Synt.comm _ = fin-SplitQuotientedChoice
nonDetFiniteVars Synt.idem _ = fin-SplitQuotientedChoice

nonDetFiniteArity : ∀ Oᵢ → SplitQuotientedChoiceω (Arity Oᵢ)
nonDetFiniteArity `<|> = quotientedChoiceBool
nonDetFiniteArity `fail = quotientedChoice⊥

open import FreeMonad.IsFree (full-theory ℕ𝔻 NonDetLaws nonDetFiniteArity nonDetFiniteVars)

module SyntExamples where
  open Synt

  ≈ₜ-comm : (x y : Syntax ℕ𝔻 A) → x <|> y ≈ₜ y <|> x
  ≈ₜ-comm x y _ ϕ in-theory k =
        cong (ϕ ∘ (`<|> ,_)) (funExt (bool refl refl))
     ⨾  in-theory comm _ (interp ℕ𝔻 ϕ k ∘ (λ { zero → x ; (suc zero) → y }))
     ⨾  cong (ϕ ∘ (`<|> ,_)) (funExt (bool refl refl))

ℕ𝔻-theory = full-theory ℕ𝔻 NonDetLaws nonDetFiniteArity nonDetFiniteVars
open import FreeMonad.Quotiented ℕ𝔻-theory

NonDet : Type a → Type a
NonDet = Term

infixr 5 _<|>_
_<|>_ : NonDet A → NonDet A → NonDet A
xs <|> ys = opₜ (`<|> , λ i → if i then ys else xs)

fail : NonDet A
fail = opₜ (`fail , absurd)

module _ {A : Type a} where
  <|>-comm :  (x y : NonDet A) → (x <|> y) ≡ (y <|> x)
  <|>-comm =
    elimProp2/
      (λ _ _ → squash/ _ _)
      λ x y → cong ([_]ₜ ∘ Synt.op ∘ (_,_ `<|>)) (funExt (bool refl refl))
            ⨾ sym (eq/ _ _ (eqₜ Synt.comm ⟨⟩ (λ { zero → y ; (suc zero) → x })))
            ⨾ cong ([_]ₜ ∘ Synt.op ∘ (_,_ `<|>)) (funExt (bool refl refl))

  <|>-idem :  (x : NonDet A) → (x <|> x) ≡ x
  <|>-idem =
    elimProp/
      (λ _ → squash/ _ _)
      λ x → cong ([_]ₜ ∘ Synt.op ∘ (_,_ `<|>)) (funExt (bool refl refl))
          ⨾ eq/ _ _ (eqₜ Synt.idem ⟨⟩ (λ { zero → x }))

  <|>-assoc :  (x y z : NonDet A) → (x <|> y) <|> z ≡ x <|> (y <|> z)
  <|>-assoc =
    elimProp3/
      (λ _ _ _ → squash/ _ _)
      λ x y z → cong ([_]ₜ ∘ Synt.op ∘ _,_ `<|>) (funExt (bool (cong (Synt.op ∘ _,_ `<|>) (funExt (bool refl refl))) refl ) )
          ⨾ (eq/ _ _ (eqₜ Synt.assoc ⟨⟩ (λ { zero → x ; (suc zero) → y ; (suc (suc _)) → z })))
          ⨾ cong ([_]ₜ ∘ Synt.op ∘ _,_ `<|>) (funExt (bool  refl (cong (Synt.op ∘ _,_ `<|>) (funExt (bool refl refl)))))

  <|>-idˡ :  (x : NonDet A) → fail <|> x ≡ x
  <|>-idˡ =
    elimProp/
      (λ _ → squash/ _ _)
      λ x → cong ([_]ₜ ∘ Synt.op ∘ _,_ `<|>) (funExt (bool (cong (Synt.op ∘ _,_ `fail) (funExt (λ ()))) refl) ) ⨾
            (eq/ _ _ (eqₜ Synt.idˡ ⟨⟩ (λ { zero → x })))


one-of : List A → NonDet A
one-of xs = [ Synt.one-of xs ]ₜ

or-idʳ : ∀ x → x || false ≡ x
or-idʳ false = refl
or-idʳ true  = refl

or-assoc :  ∀ x y z →
            (x || y) || z ≡ x || (y || z)
or-assoc false  _ _ = refl
or-assoc true   _ _ = refl

or-comm : ∀ x y → x || y ≡ y || x
or-comm false false = refl
or-comm false true  = refl
or-comm true  false = refl
or-comm true  true  = refl

or-idem : ∀ x → x || x ≡ x
or-idem false = refl
or-idem true  = refl

module _ {ν : Type a} (p : ν → Bool) where
  any? : NonDet ν → Bool
  any? = interpₜ ϕ p ϕ-resp isSetBool
    where
    ϕ : ℕ𝔻 -Alg[ Bool ]
    ϕ (`<|>   , k) = k false || k true
    ϕ (`fail  , k) = false

    ϕ-resp : ϕ Models NonDetLaws
    ϕ-resp Synt.assoc _ ρ =
      or-assoc (ρ 0) (ρ 1) (ρ 2)

    ϕ-resp Synt.idˡ   _ ρ =
                              false || ρ 0 ≡⟨⟩
                              ρ 0 ∎
    ϕ-resp Synt.comm  _ ρ =
                              ρ 0 || ρ 1 ≡⟨ or-comm (ρ 0) (ρ 1) ⟩
                              ρ 1 || ρ 0 ∎
    ϕ-resp Synt.idem  _ ρ =
                              ρ 0 || ρ 0 ≡⟨ or-idem (ρ 0) ⟩
                              ρ 0 ∎

open import Truth.Logic
import Truth
open Truth using (ProofOf; IsProp)

module _ {ν : Type a} (𝒫 : ν → Truth.Ω p) where
  open import Truth.Definition p
  open import Truth.Combinators {p}
  open import Truth.Logic

  All : NonDet ν → Ω
  All = interpₜ Φ 𝒫 Φ-resp isSetΩ
    where
    Φ : ℕ𝔻 -Alg[ Ω ]
    Φ (`<|>   , k) = k false |∧| k true
    Φ (`fail  , k) = True

    Φ-resp : Φ Models NonDetLaws
    Φ-resp Synt.idˡ    _ ρ = ∧-id _
    Φ-resp Synt.assoc  _ ρ = ∧-assoc _ _ _
    Φ-resp Synt.comm   _ ρ = ∧-com _ _
    Φ-resp Synt.idem   _ ρ = ∧-idem _

open import Data.List.Membership

open import Data.Set

set-alg : ℕ𝔻 -Alg[ 𝒦 A ]
set-alg (`fail  , k) = ∅
set-alg (`<|>   , k) = k false ∪ k true

set-resp : (set-alg ⦂ ℕ𝔻 -Alg[ 𝒦 A ]) Models NonDetLaws
set-resp Synt.idˡ   γ ρ = refl
set-resp Synt.assoc γ ρ = ∪-assoc (ρ 0) (ρ 1) (ρ 2)
set-resp Synt.comm  γ ρ = ∪-com (ρ 0) (ρ 1)
set-resp Synt.idem  γ ρ = ∪-idem (ρ 0)

from-set-alg : ψ A (Term A)
from-set-alg .fst ∅ = fail
from-set-alg .fst (x ∷ _ ⟨ P⟨xs⟩ ⟩) = return x <|> P⟨xs⟩
from-set-alg .snd .c-trunc _ = squash/
from-set-alg .snd .c-com x y _ xs =
    sym (<|>-assoc (return x) (return y) xs)
  ⨾ cong (_<|> xs) (<|>-comm  (return x) (return y))
  ⨾
  <|>-assoc (return y) (return x) xs
from-set-alg .snd .c-dup x _ xs =
  sym (<|>-assoc (return x) (return x) xs) ⨾ cong (_<|> xs) (<|>-idem (return x))

<|>-hom : (xs ys : 𝒦 A) → Data.Set.⟦ from-set-alg ⟧ (xs ∪ ys) ≡ Data.Set.⟦ from-set-alg ⟧ xs <|> Data.Set.⟦ from-set-alg ⟧ ys
<|>-hom xs ys = Data.Set.⟦ lemma ys ⟧ xs
  where
  lemma : (ys : 𝒦 A) → Ψ[ xs ⦂ 𝒦 A ] ↦ (Data.Set.⟦ from-set-alg ⟧ (xs ∪ ys) ≡ Data.Set.⟦ from-set-alg ⟧ xs <|> Data.Set.⟦ from-set-alg ⟧ ys)
  lemma ys .fst ∅ = sym (<|>-idˡ _)
  lemma ys .fst (x ∷ xs ⟨ Pxs ⟩) = cong (return x <|>_) Pxs ⨾ sym (<|>-assoc (return x) (Data.Set.⟦ from-set-alg ⟧ xs) (Data.Set.⟦ from-set-alg ⟧ ys))
  lemma ys .snd = prop-coh λ _ → squash/ _ _

term-iso : {A : Type} → NonDet A ⇔ 𝒦 A
term-iso .fun = interpₜ set-alg (λ x → x ∷ ∅) set-resp trunc
term-iso .inv = Data.Set.⟦ from-set-alg ⟧

term-iso .leftInv = elimProp/ (λ _ → squash/ _ _) (Synt.elim-s _ _ 
  λ { (Synt.var x) → <|>-comm (return x) fail ⨾ <|>-idˡ (return x)
    ; (Synt.op (`fail , k) xs) → cong ([_]ₜ ∘ Synt.op ∘ _,_ `fail) (funExt (λ ()))
    ; (Synt.op (`<|> , k) xs) →
      Data.Set.⟦ from-set-alg ⟧ (Synt.interp _ set-alg (_∷ ∅) (Synt.op (`<|> , k))) ≡⟨⟩
      Data.Set.⟦ from-set-alg ⟧ (Synt.interp _ set-alg (_∷ ∅) (k false) ∪ Synt.interp _ set-alg (_∷ ∅) (k true)) ≡⟨ <|>-hom (Synt.interp _ set-alg (_∷ ∅) (k false)) _ ⟩
      Data.Set.⟦ from-set-alg ⟧ (Synt.interp _ set-alg (_∷ ∅) (k false)) <|> Data.Set.⟦ from-set-alg ⟧ (Synt.interp _ set-alg (_∷ ∅) (k true)) ≡⟨ cong₂ _<|>_ (xs false) (xs true) ⟩
      [ k false ]ₜ <|> [ k true ]ₜ ≡⟨⟩
      [ Synt.op (`<|> , bool (k false) (k true)) ]ₜ ≡⟨ cong ([_]ₜ ∘ Synt.op ∘ _,_ `<|>) (funExt (bool refl refl)) ⟩
      [ Synt.op (`<|> , k) ]ₜ ∎
    })
term-iso .rightInv = Data.Set.⟦ lemma ⟧
  where
  lemma : {A : Type} → Ψ[ xs ⦂ 𝒦 A ] ↦ (interpₜ set-alg (_∷ ∅) set-resp trunc (Data.Set.⟦ from-set-alg ⟧ xs) ≡ xs)
  lemma .fst ∅ = refl
  lemma .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    interpₜ set-alg (_∷ ∅) set-resp trunc (return x <|> Data.Set.⟦ from-set-alg ⟧ xs) ≡⟨⟩
    interpₜ set-alg (_∷ ∅) set-resp trunc (opₜ (`<|> , bool (return x) (Data.Set.⟦ from-set-alg ⟧ xs))) ≡⟨ interpₜ-opₜ set-alg (_∷ ∅) set-resp trunc `<|> (bool (return x) (Data.Set.⟦ from-set-alg ⟧ xs)) ⟩
    set-alg (`<|> , bool (interpₜ set-alg (_∷ ∅) set-resp trunc (return x)) (interpₜ set-alg (_∷ ∅) set-resp trunc  (Data.Set.⟦ from-set-alg ⟧ xs))) ≡⟨⟩
    interpₜ set-alg (_∷ ∅) set-resp trunc (return x) ∪ (interpₜ set-alg (_∷ ∅) set-resp trunc  (Data.Set.⟦ from-set-alg ⟧ xs)) ≡⟨⟩
    x ∷ interpₜ set-alg (_∷ ∅) set-resp trunc (Data.Set.⟦ from-set-alg ⟧ xs) ≡⟨ cong (x ∷_) P⟨xs⟩ ⟩
    x ∷ xs ∎
  lemma .snd = eq-coh


-- interp-opₜ-com-[]  :  (k : A → Syntax B) (xs : Syntax A)
--                    →  [ interp op k xs ] ≡ interp opₜ ([_] ∘ k) xs


private variable q : Level

module _ where
  open Truth using (Ω)
  All-map : {P : A → Ω p} {Q : A → Ω q}
          → (f : ∀ x → ProofOf (P x) → ProofOf (Q x))
          → ∀ xs
          → ProofOf (All P xs) → ProofOf (All Q xs)
  All-map {Q = Q} f =
    elimProp/ (λ x → isProp→ (All Q x .IsProp) )
      (Synt.elim-s _ _ (λ { (Synt.var x) → f x
                          ; (Synt.op (`<|> , k) P⟨xs⟩) p → P⟨xs⟩ false (p .fst) , P⟨xs⟩ true (p .snd)
                          ; (Synt.op (`fail , k) P⟨xs⟩) _ → _ }) )

all-in : (xs : List A) → ProofOf (All (λ x → Ω∣ x ∈ xs ∣) (one-of xs))
all-in []        = _
all-in (x ∷ xs) .fst = ∣ 0 , refl ∣
all-in (x ∷ xs) .snd =
  All-map (λ x → ∥map∥ λ { (i , p) → suc i , p })
          (one-of xs)
          (all-in xs)

open import Hoare.Definition ℕ𝔻-theory
open import Hoare.Lemmas     ℕ𝔻-theory
open import Hoare.Calculus   ℕ𝔻-theory
open import Truth

guard : Bool → NonDet ⊤
guard = bool fail (return ⟨⟩)

guard-hoare : ∀ p → ⟅⟆ guard p ⟅ return (|T| {ℓzero} p) ⟆
guard-hoare false .proof k = refl
guard-hoare true  .proof k = cong (k ⟨⟩) (|→|-id _)
