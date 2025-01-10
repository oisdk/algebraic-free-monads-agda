{-# OPTIONS --safe #-}

module Data.Bool.Properties where

open import Data.Bool
open import Decidable
open import Path
open import Data.Unit
open import HLevels
open import Data.Empty.Properties
open import Data.Unit.Properties

discreteBool : Discrete Bool
discreteBool = from-bool-eq
  record { _≡ᴮ_ = bool′ ! (λ x → x)
         ; sound = λ { false false p → refl ; true true p → refl }
         ; complete = λ { false → tt ; true → tt }
         }

isSetBool : isSet Bool
isSetBool = Discrete→isSet discreteBool

isPropT : ∀ b → isProp (T b)
isPropT false = isProp⊥
isPropT true  = isProp⊤

open import Data.Empty

false≢true : false ≢ true
false≢true p = subst (bool ⊤ ⊥) p tt

true≢false : true ≢ false
true≢false p = subst (bool ⊥ ⊤) p tt

open import Level
open import Isomorphism
open import Data.Sigma

Bool→⇔× : (Bool → A) ⇔ (A × A)
Bool→⇔× .fun f = f false , f true
Bool→⇔× .inv (x , y) false  = x
Bool→⇔× .inv (x , y) true   = y
Bool→⇔× .rightInv _ = refl
Bool→⇔× .leftInv f i false = f false
Bool→⇔× .leftInv f i true  = f true

||-assoc : (x y z : Bool) → (x || y) || z ≡ x || (y || z)
||-assoc false y z = refl
||-assoc true  y z = refl

||-idʳ : ∀ x → x || false ≡ x
||-idʳ false = refl
||-idʳ true  = refl

||-annʳ : ∀ x → x || true ≡ true
||-annʳ false = refl
||-annʳ true  = refl

||-comm : (x y : Bool) → x || y ≡ y || x
||-comm false y = sym (||-idʳ y)
||-comm true  y = sym (||-annʳ y)

||-idem : ∀ x → x || x ≡ x
||-idem false  = refl
||-idem true   = refl

&&-assoc : (x y z : Bool) → (x && y) && z ≡ x && (y && z)
&&-assoc false y z = refl
&&-assoc true  y z = refl

&&-idʳ : ∀ x → x && true ≡ x
&&-idʳ false = refl
&&-idʳ true  = refl

&&-annʳ : ∀ x → x && false ≡ false
&&-annʳ false = refl
&&-annʳ true  = refl

&&-comm : (x y : Bool) → x && y ≡ y && x
&&-comm false y = sym (&&-annʳ y)
&&-comm true  y = sym (&&-idʳ  y)

&&-idem : ∀ x → x && x ≡ x
&&-idem false = refl
&&-idem true = refl
