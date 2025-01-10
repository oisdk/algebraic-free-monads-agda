{-# OPTIONS --safe #-}

module Function.Properties where

open import Prelude

Discrete-↢ : A ↢ B → Discrete A → Discrete B
Discrete-↢ (f , inj) _≟_ x y = map-dec inj (λ fx≢fy → fx≢fy ∘ cong f) (f x ≟ f y)

Discrete-↠! : A ↠! B → Discrete A → Discrete B
Discrete-↠! = Discrete-↢ ∘ ↠!⇒↢
