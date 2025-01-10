{-# OPTIONS --safe #-}

module Data.Maybe.Properties where

open import Prelude 
open import Cubical.Foundations.Everything using (JRefl; _≃_; isOfHLevel; isOfHLevelRetract; isProp→isOfHLevelSuc)
open import Data.Unit.UniversePolymorphic.Properties

module MaybePath {ℓ} {A : Type ℓ} where
  Cover : Maybe A → Maybe A → Type ℓ
  Cover nothing  nothing   = Poly-⊤
  Cover nothing  (just _)  = Poly-⊥
  Cover (just _) nothing   = Poly-⊥
  Cover (just a) (just a') = a ≡ a'

  reflCode : (c : Maybe A) → Cover c c
  reflCode nothing  = Poly-tt
  reflCode (just b) = refl

  encode : ∀ c c' → c ≡ c' → Cover c c'
  encode c _ = J (λ c' _ → Cover c c') (reflCode c)

  encodeRefl : ∀ c → encode c c refl ≡ reflCode c
  encodeRefl c = JRefl (λ c' _ → Cover c c') (reflCode c)

  decode : ∀ c c' → Cover c c' → c ≡ c'
  decode nothing  nothing  _ = refl
  decode (just _) (just _) p = cong just p

  decodeRefl : ∀ c → decode c c (reflCode c) ≡ refl
  decodeRefl nothing  = refl
  decodeRefl (just _) = refl

  decodeEncode : ∀ c c' → (p : c ≡ c') → decode c c' (encode c c' p) ≡ p
  decodeEncode c _ =
    J (λ c' p → decode c c' (encode c c' p) ≡ p)
      (cong (decode c c) (encodeRefl c) ⨾ decodeRefl c)

  encodeDecode : ∀ c c' → (d : Cover c c') → encode c c' (decode c c' d) ≡ d
  encodeDecode nothing nothing _ = refl
  encodeDecode (just a) (just a') =
    J (λ a' p → encode (just a) (just a') (cong just p) ≡ p) (encodeRefl (just a))

  Cover≃Path : ∀ c c' → Cover c c' ≃ (c ≡ c')
  Cover≃Path c c' = isoToEquiv
    (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  Cover≡Path : ∀ c c' → Cover c c' ≡ (c ≡ c')
  Cover≡Path c c' = isoToPath
    (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  isOfHLevelCover : (n : ℕ)
    → isOfHLevel (suc (suc n)) A
    → ∀ c c' → isOfHLevel (suc n) (Cover c c')
  isOfHLevelCover n p nothing  nothing   = isOfHLevelPoly⊤ _
  isOfHLevelCover n p nothing  (just a') = isProp→isOfHLevelSuc _ λ ()
  isOfHLevelCover n p (just a) nothing   = isProp→isOfHLevelSuc _ λ ()
  isOfHLevelCover n p (just a) (just a') = p a a'

isOfHLevelMaybe : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → isOfHLevel (suc (suc n)) A
  → isOfHLevel (suc (suc n)) (Maybe A)
isOfHLevelMaybe n lA c c' =
  isOfHLevelRetract (suc n)
    (MaybePath.encode c c')
    (MaybePath.decode c c')
    (MaybePath.decodeEncode c c')
    (MaybePath.isOfHLevelCover n lA c c')
