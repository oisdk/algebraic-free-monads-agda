{-# OPTIONS --safe #-}

module HITs.SetTruncation where

open import Cubical.HITs.SetTruncation
  using
    ( ∥_∥₂
    ; ∣_∣₂
    ; squash₂
    )
  renaming
    ( rec to ∥rec∥₂
    ; elim to ∥elim∥₂
    )
  public
