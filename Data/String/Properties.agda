{-# OPTIONS --safe #-}

module Data.String.Properties where

open import Data.String
open import Data.Nat.Properties
open import Decidable
open import Data.Sigma
open import Path
open import Identity
open import Function
open import Agda.Builtin.Char
open import Agda.Builtin.Char.Properties

discreteChar : Discrete Char
discreteChar =
  inj-discrete
    (primCharToNat , id-to-path ∘ primCharToNatInjective _ _ ∘ path-to-id)
    discreteNat

open import HLevels

isSetChar : isSet Char
isSetChar = Discrete→isSet discreteChar

open import Cubical.Data.List.Properties using (isOfHLevelList)

isSetString : isSet String
isSetString = isOfHLevelList 0 isSetChar
