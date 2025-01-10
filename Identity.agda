{-# OPTIONS --safe #-}

module Identity where

open import Agda.Builtin.Equality
  renaming (_≡_ to Id; refl to Id-refl)
  public
open import Path
open import Level

private
  variable
    x y z : A

id-to-path : Id x y → x ≡ y
id-to-path Id-refl = refl

path-to-id : x ≡ y → Id x y
path-to-id {x = x} p = subst (Id x) p Id-refl

Id-sym : Id x y → Id y x
Id-sym Id-refl = Id-refl

Id-trans : Id x y → Id y z → Id x z
Id-trans Id-refl Id-refl = Id-refl
