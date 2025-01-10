{-# OPTIONS --safe #-}

module Prelude where

open import Data.Sigma public
open import Data.Sigma.Properties public
  using (PathPΣ; ΣPathP; Σ≡Prop; ⇔-Σ-swap; ⇔-Σ-assoc)
open import Data.Empty public
open import Data.Empty.Properties public
open import Equiv public
open import Data.Unit public
open import Data.Bool public
open import Data.Nat public
open import Data.Fin public
open import Data.Maybe public
open import Level public
open import Level.Literals public
open import Function public
open import Function.Reasoning public
open import Path public
open import Path.Reasoning public
open import Data.Sum public
open import Isomorphism public
open import Data.List public
open import HLevels public
open import Decidable public
open import Inspect public
open import Literals.Number public
open import Identity public
open import Data.Bool.Properties public
open import Strict public
open import Data.Lift public

open import Data.Unit.UniversePolymorphic
  renaming (⊤ to Poly-⊤; tt to Poly-tt)
  public

open import Data.Empty.UniversePolymorphic
  renaming (⊥ to Poly-⊥)
  public

open import HITs.SetQuotients public
open import HITs.SetTruncation public
open import HITs.PropositionalTruncation public

open import Data.String using (Char; String; primStringToList) public
