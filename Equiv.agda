{-# OPTIONS --safe #-}

module Equiv where

open import Cubical.Foundations.Equiv
  using
    ( _≃_
    ; equiv-proof
    ; isEquiv
    ; equivToIso
    )
  renaming
    ( compEquiv to ≃-trans
    ; invEquiv  to ≃-sym
    )
  public
open import Cubical.Foundations.Everything
  using (ua)
  public
