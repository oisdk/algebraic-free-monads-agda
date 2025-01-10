{-# OPTIONS --safe #-}

module Data.Bool where

open import Level
open import Agda.Builtin.Bool using (Bool; true; false) public
open import Data.Unit
open import Data.Empty

bool : ∀ {ℓ} {P : Bool → Type ℓ} (f : P false) (t : P true) (x : Bool) → P x
bool f t false  = f
bool f t true   = t
{-# INLINE bool #-}

bool′ : A → A → Bool → A
bool′ = bool
{-# INLINE bool′ #-}

infixr 0 if-syntax
if-syntax : Bool → A → A → A
if-syntax p t f = bool f t p

syntax if-syntax p t f = if p then t else f

! : Bool → Bool
! = bool′ true false 

infixl 6 _||_
_||_ : Bool → Bool → Bool
x || y = bool′ y true x

infixl 7 _&&_
_&&_ : Bool → Bool → Bool
x && y = bool′ false y x

T : Bool → Type
T = bool′ ⊥ ⊤
