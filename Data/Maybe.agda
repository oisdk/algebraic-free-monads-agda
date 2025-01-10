{-# OPTIONS --safe #-}

module Data.Maybe where

open import Agda.Builtin.Maybe public
open import Function
open import Level
open import Path

maybe : {B : Maybe A → Type b} → B nothing → (∀ x → B (just x)) → ∀ x → B x
maybe b f (just x) = f x
maybe b f nothing = b

maybe′ : B → (A → B) → Maybe A → B
maybe′ = maybe

from-maybe : A → Maybe A → A
from-maybe d = maybe′ d id

just-inj : Injective (just {A = A})
just-inj {x = x} = cong (maybe′ x id)

map-maybe : (A → B) → Maybe A → Maybe B
map-maybe f = maybe′ nothing (just ∘ f)

open import Data.Bool

is-just : Maybe A → Bool
is-just = maybe′ false (const true)
