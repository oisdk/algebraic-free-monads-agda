{-# OPTIONS --cubical --safe #-}

module Path where

open import Cubical.Foundations.Everything
  using ( _≡_
        ; sym
        ; refl
        ; subst
        ; transport
        ; Path
        ; PathP
        ; I
        ; i0
        ; i1
        ; funExt
        ; cong
        ; toPathP
        ; cong₂
        ; ~_
        ; _∧_
        ; _∨_
        ; hcomp
        ; transp
        ; J
        ; JRefl
        ; substRefl
        ; transportRefl
        ; transport-filler
        ; fromPathP
        ; symP
        )
  renaming (subst2 to subst₂)
  public

open import Data.Empty using (¬_)
open import Level

infixr 2 _⨾_
_⨾_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_⨾_ = Cubical.Foundations.Everything._∙_

infix 4 _≢_
_≢_ : {A : Type a} → A → A → Type a
x ≢ y = ¬ (x ≡ y)

infix 4 PathP-syntax
PathP-syntax = PathP
{-# DISPLAY PathP-syntax = PathP #-}

syntax PathP-syntax (λ i → Ty) lhs rhs = lhs ≡[ i ↦ Ty ]≡ rhs
