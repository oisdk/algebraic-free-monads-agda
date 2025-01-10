{-# OPTIONS --lossy-unification --safe #-}


open import Prelude renaming (tt to ⟨⟩)
open import Signatures
open import FinitenessConditions
open import FreeMonad.PackagedTheory
open import Data.String.Properties renaming (discreteChar to _≟_)

module Effects.Parser.TreeParser
  (choiceString : SplitQuotientedChoiceω String)
  where

open import Effects.Parser choiceString

open import Hoare.Definition ℙ-theory
open import Hoare.Calculus ℙ-theory
open import Hoare.Lemmas ℙ-theory

open Signature (FullTheory.𝔽 ℙ-theory)

open import Truth
open import Data.Tree

parse-tree : ℕ → Term Tree
parse-tree zero     =  fail
parse-tree (suc n)  =       (do char '♢'; return ♢)
                       <|>  (do char '♠'; return ♠)
                       <|>  (do char '('; l ← parse-tree n
                                char '*'; r ← parse-tree n
                                char ')'; return (l ⊛ r))
print : Tree → String
print ♢        = "♢"
print ♠        = "♠"
print (l ⊛ r)  = "(" ++ print l ++ "*" ++ print r ++ ")"

tree-alt-di : Term Tree
tree-alt-di = do char '♢'; return ♢

tree-alt-sp : Term Tree
tree-alt-sp = do char '♠'; return ♠

tree-n-branch : ℕ → Term Tree
tree-n-branch n =
  (do char '('
      l ← parse-tree n
      char '*'
      r ← parse-tree n
      char ')'
      return (l ⊛ r))

sp-di-ne-lemma : ∀ s →
  ⟅ remaining ('♠' ∷ s) ⟆ v ← (do char '♢'; return ♢) ⟅ return (♠ |≡| v) ⟨∧⟩ remaining s ⟆
sp-di-ne-lemma s =
  char-ne (λ v → return (♠ |≡| v) ⟨∧⟩ remaining s , sef-<$> _ _ (sef-rem s) , det-<$> _ _ (det-rem s) ) '♠' '♢' s (return ♢) (from-dec-false ('♠' ≟ '♢') _)

something : ∀ s →
  ⟅ remaining ('♠' ∷ s) ⟆ char '♢' ⟅ return ('♠' |≡| '♢') ⟨∧⟩ remaining s ⟆
something = parse-char '♠' '♢'

sp-lemma : ∀ s →
  ⟅ remaining ('♠' ∷ s) ⟆ v ← (do char '♠'; return ♠) ⟅ return (♠ |≡| v) ⟨∧⟩ remaining s ⟆
sp-lemma s =
  parse-char '♠' '♠' s ⦂
    ⟅ remaining (print ♠ ++ s) ⟆ char '♠'        ⟅ return ('♠' |≡| '♠') ⟨∧⟩ remaining s ⟆
  ⇒⟨ ⟅∙⟆≡ (λ _ → cong (λ e → return e ⟨∧⟩ remaining s) (proves ∣ refl ∣ ⨾ sym (proves ∣ refl ∣))) ⟩
    ⟅ remaining (print ♠ ++ s) ⟆ char '♠'        ⟅ return (♠ |≡| ♠) ⟨∧⟩ remaining s ⟆
  ⇒⟨ focus (const ♠) ⟩
    ⟅ remaining (print ♠ ++ s) ⟆ v ← tree-alt-sp ⟅ return (♠ |≡| v) ⟨∧⟩ remaining s ⟆

di-lemma : ∀ s →
  ⟅ remaining (print ♢ ++ s) ⟆ v ← tree-alt-di ⟅ return (♢ |≡| v) ⟨∧⟩ remaining s ⟆
di-lemma s =
  parse-char '♢' '♢' s ⦂
    ⟅ remaining (print ♢ ++ s) ⟆ char '♢'        ⟅ return ('♢' |≡| '♢') ⟨∧⟩ remaining s ⟆
  ⇒⟨ ⟅∙⟆≡ (λ _ → cong (λ e → return e ⟨∧⟩ remaining s) (proves ∣ refl ∣ ⨾ sym (proves ∣ refl ∣))) ⟩
    ⟅ remaining (print ♢ ++ s) ⟆ char '♢'        ⟅ return (♢ |≡| ♢) ⟨∧⟩ remaining s ⟆
  ⇒⟨ focus (const ♢) ⟩
    ⟅ remaining (print ♢ ++ s) ⟆ v ← tree-alt-di ⟅ return (♢ |≡| v) ⟨∧⟩ remaining s ⟆

left-def : Tree → Tree → Tree
left-def d = from-maybe d ∘ left

right-def : Tree → Tree → Tree
right-def d = from-maybe d ∘ right

tr-lemma₁ :  ∀ n l r s →
    ⟅ remaining (print (l ⊛ r) ++ s) ⟆ l′ ← char '(' >> parse-tree n ⟅ return (l |≡| l′) ⟨∧⟩ remaining ("*" ++ print r ++ ")" ++ s) ⟆ →
    ⟅ remaining (print (l ⊛ r) ++ s) ⟆ l′ ← (char '(' >> parse-tree n) << char '*'  ⟅ return (l |≡| l′) ⟨∧⟩ (return ('*' |≡| '*') ⟨∧⟩ remaining (print r ++ ")" ++ s)) ⟆
tr-lemma₁ n l r s e =
  seq-<< (⟨remaining⟩ (print (l ⊛ r) ++ s)) (λ _ → _ , sef-<$> _ _ (sef-rem ("*" ++ print r ++ ")" ++ s)) , det-<$> _ _ ( det-rem ("*" ++ print r ++ ")" ++ s)))
    (λ l′ → _ , sef-<$> _ _ (sef-<$> _ _ (sef-rem (print r ++ ")" ++ s))) , det-<$> _ _ (det-<$> _ _ (det-rem (print r ++ ")" ++ s))) ) e
      λ l′ → ⟅∧⟆ {p = (l |≡| l′)} (⟨remaining⟩ ("*" ++ print r ++ ")" ++ s)) (λ _ → _ , sef-<$> _ _ (sef-rem (print r ++ ")" ++ s)) , det-<$> _ _ (det-rem (print r ++ ")" ++ s))  ) (parse-char '*' '*' (print r ++ ")" ++ s))

tr-lemma₃ : ∀ n l r s →
      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ (l′ , r′) ← (((char '(' >> parse-tree n) << char '*') ⨾, const (parse-tree n))  ⟅ (return (l |≡| l′) ⟨∧⟩ return (r |≡| r′)) ⟨∧⟩ remaining (")" ++ s) ⟆ →
      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ (l′ , r′) ← (((char '(' >> parse-tree n) << char '*') ⨾, const (parse-tree n)) << char ')' ⟅ return (l |≡| l′) ⟨∧⟩ return (r |≡| r′) ⟨∧⟩ (return (')' |≡| ')' ) ⟨∧⟩ remaining s) ⟆
tr-lemma₃ n l r s e =
  seq-<< (⟨remaining⟩ (print (l ⊛ r) ++ s))
    (λ _ → _ , sef-<$> _ _ (sef-rem (")" ++ s)) , det-<$> _ _ (det-rem (")" ++ s)))
    (λ _ → _ , sef-<$> _ _ (sef-<$> _ _ (sef-rem s)) , det-<$> _ _ (det-<$> _ _ (det-rem s)))
    e λ _ → ⟅∧⟆
    (⟨remaining⟩ (")" ++ s))
    (λ _ → _ , sef-<$> _ _ (sef-rem s) , det-<$> _ _ (det-rem s) )
    (parse-char ')' ')' s)

open import Effects.NonDetState String choiceString isSetString as NDS using (sef-<|>; fail-absurd; <|>-conj)


mutual
  tr-lemma₂ : ∀ n l r s →
        ⟅ remaining (print (l ⊛ r) ++ s) ⟆ l′ ← (char '(' >> parse-tree n) << char '*'  ⟅ return (l |≡| l′) ⟨∧⟩ remaining (print r ++ ")" ++ s) ⟆ →
        ⟅ remaining (print (l ⊛ r) ++ s) ⟆ (l′ , r′) ← (((char '(' >> parse-tree n) << char '*') ⨾, const (parse-tree n))  ⟅ return (l |≡| l′) ⟨∧⟩ (return (r |≡| r′) ⟨∧⟩ remaining (")" ++ s)) ⟆
  tr-lemma₂ n l r s e =
     seq (⟨remaining⟩ (print (l ⊛ r) ++ s)) (λ _ → _ , sef-<$> _ _ (sef-rem (print r ++ ")" ++ s) ) , det-<$> _ _ (det-rem (print r ++ ")" ++ s)) )
       (λ _ → _ ,  sef-<$> _ _ (sef-<$> _ _ (sef-rem (")" ++ s))) , det-<$> _ _ (det-<$> _ _ (det-rem (")" ++ s)))  ) e
         λ l′ →         ⟅∧⟆ {p = l |≡| l′}
                          (⟨remaining⟩ (print r ++ ")" ++ s) )
                          (λ _ → _ , sef-<$> _ _ (sef-rem (")" ++ s)) , det-<$> _ _ (det-rem (")" ++ s)))
                          (round-trip n r (")" ++ s))


  tr-lemma : ∀ n l r s → ⟅ remaining (print (l ⊛ r) ++ s) ⟆ v ← tree-n-branch n ⟅ return ((l ⊛ r) |≡| v) ⟨∧⟩ remaining s ⟆
  tr-lemma n l r s =
    parse-char '(' '(' (tail (print (l ⊛ r) ++ s)) ⦂

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ char '(' ⟅ return ('(' |≡| '(') ⟨∧⟩ remaining (tail (print (l ⊛ r) ++ s)) ⟆
      ⇒⟨ ⟅∙⟆≡ (λ _ → cong (λ e → return e ⟨∧⟩ remaining (tail (print (l ⊛ r) ++ s))) (proves ∣ refl ∣)) ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ char '(' ⟅ return True ⟨∧⟩ remaining (tail (print (l ⊛ r) ++ s)) ⟆
      ⇒⟨ ⟅∙⟆≡ (λ _ → True⟨∧⟩ _) ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ char '(' ⟅ remaining (tail (print (l ⊛ r) ++ s)) ⟆

      ⇒⟨ (seq⁻ (⟨remaining⟩ (print (l ⊛ r) ++ s)) (λ _ → ⟨remaining⟩ ((print l ++ "*" ++ print r ++ ")") ++ s)) (λ _ → _ , sef-<$> _ _ (sef-rem  ("*" ++ print r ++ ")" ++ s)) , det-<$> _ _ ( det-rem ("*" ++ print r ++ ")" ++ s))) (λ _ → ≡⟅∙⟆ (cong remaining (sym (++-assoc (print l) _ _ ⨾ cong (print l ++_) (++-assoc "*" _ _ ⨾ cong ("*" ++_) (++-assoc (print r) _ _))))) (round-trip n l (("*" ++ print r ++ ")" ++ s))) )) ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ l′ ← char '(' >> parse-tree n ⟅ return (l |≡| l′) ⟨∧⟩ remaining ("*" ++ print r ++ ")" ++ s) ⟆

      ⇒⟨ tr-lemma₁ n l r s ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ l′ ← (char '(' >> parse-tree n) << char '*'  ⟅ return (l |≡| l′) ⟨∧⟩ (return ('*' |≡| '*') ⟨∧⟩ remaining (print r ++ ")" ++ s)) ⟆

      ⇒⟨ ⟅∙⟆≡ (λ l′ → cong (return (l |≡| l′) ⟨∧⟩_) ( cong (_⟨∧⟩ remaining (print r ++ ")" ++ s)) (cong return (proves ∣ refl ∣)) ⨾ True⟨∧⟩ _) ) ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ l′ ← (char '(' >> parse-tree n) << char '*'  ⟅ return (l |≡| l′) ⟨∧⟩ remaining (print r ++ ")" ++ s) ⟆

      ⇒⟨ tr-lemma₂ n l r s ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ (l′ , r′) ← (((char '(' >> parse-tree n) << char '*') ⨾, const (parse-tree n))  ⟅ return (l |≡| l′) ⟨∧⟩ (return (r |≡| r′) ⟨∧⟩ remaining (")" ++ s)) ⟆

      ⇒⟨ ⟅∙⟆≡ (λ { (l′ , r′) → sym (⟨∧⟩-assoc (return (l |≡| l′)) (return (r |≡| r′)) (remaining (")" ++ s)))    }) ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ (l′ , r′) ← (((char '(' >> parse-tree n) << char '*') ⨾, const (parse-tree n))  ⟅ (return (l |≡| l′) ⟨∧⟩ return (r |≡| r′)) ⟨∧⟩ remaining (")" ++ s) ⟆

      ⇒⟨ tr-lemma₃ n l r s ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ (l′ , r′) ← (((char '(' >> parse-tree n) << char '*') ⨾, const (parse-tree n)) << char ')' ⟅ return (l |≡| l′) ⟨∧⟩ return (r |≡| r′) ⟨∧⟩ (return (')' |≡| ')' ) ⟨∧⟩ remaining s) ⟆

      ⇒⟨ ⟅∙⟆≡ (λ { (l′ , r′) → sym (⟨∧⟩-assoc (return ((l |≡| l′) |∧| (r |≡| r′))) _ _) ⨾ cong (_⟨∧⟩ remaining s) (cong return (( λ { ((l″ , r″) , _) → ∥liftA2∥ (λ x y → cong₂ _⊛_ x y) l″ r″ }) iff  ∥rec∥ (isProp× (isProp× squash squash) squash) λ p → (∣ cong (left-def l) p ∣ , ∣ cong (right-def r) p ∣) , ∣ refl ∣ ))  }) ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ (l′ , r′) ← (((char '(' >> parse-tree n) << char '*') ⨾, const (parse-tree n)) << char ')' ⟅ return ((l ⊛ r) |≡| (l′ ⊛ r′)) ⟨∧⟩ remaining s ⟆

      ⇒⟨ focus (uncurry _⊛_) ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ v ← uncurry _⊛_ <$> (((char '(' >> parse-tree n) << char '*') ⨾, const (parse-tree n)) << char ')' ⟅ return ((l ⊛ r) |≡| v) ⟨∧⟩ remaining s ⟆

      ⇒⟨ subst-⟅⟆ (assoc (((char '(' >> parse-tree n) << char '*') ⨾, const (parse-tree n)) _ _ ⨾ assoc ((char '(' >> parse-tree n) << char '*') _ _ ⨾ assoc (char '(' >> parse-tree n) _ _ ⨾ assoc (char '(') _ _ ⨾ _ ⇐ char '(' ⨾/  l ⇐ parse-tree n ⨾/ assoc (char '*') _ _ ⨾ _ ⇐ char '*' ⨾/ assoc (parse-tree n) _ _ ⨾ r ⇐ parse-tree n ⨾/ assoc (char ')') _ _ ) ⟩

      ⟅ remaining (print (l ⊛ r) ++ s) ⟆ v ← tree-n-branch n ⟅ return ((l ⊛ r) |≡| v) ⟨∧⟩ remaining s ⟆




  round-trip : ∀ n t → print t ∈ parse-tree n ↦ t
  round-trip zero t s =
    fail-absurd _ ⦂
      (⟅⟆ v ← parse-tree zero ⟅ return (t |≡| v) ⟨∧⟩ remaining s ⟆) ⇒⟨ weaken ⟨return True ⟩ (λ v → return (t |≡| v) ⟨∧⟩ remaining s , sef-<$> _ _ (sef-rem s) , det-<$> _ _ (det-rem s)) (⟨remaining⟩ (print t ++ s)) (⟅→⟆True _ _) ⟩
      ⟅ remaining (print t ++ s) ⟆ v ← parse-tree zero ⟅ return (t |≡| v) ⟨∧⟩ remaining s ⟆

  round-trip (suc n)  ♢        s =
    di-lemma s
    ⟨<|>⟩
    char-ne (λ v → return (♢ |≡| v) ⟨∧⟩ remaining s , sef-<$> _ _ (sef-rem s) , det-<$> _ _ (det-rem s) ) '♢' '♠' s (return ♠) (from-dec-false ('♢' ≟ '♠') _)
    ⟨<|>⟩
    char-ne (λ v → return (♢ |≡| v) ⟨∧⟩ remaining s , sef-<$> _ _ (sef-rem s) , det-<$> _ _ (det-rem s) ) '♢' '(' s _ (from-dec-false ('♢' ≟ '(') _)

  round-trip (suc n) ♠ s =
    char-ne (λ v → return (♠ |≡| v) ⟨∧⟩ remaining s , sef-<$> _ _ (sef-rem s) , det-<$> _ _ (det-rem s) ) '♠' '♢' s (return ♢) (from-dec-false ('♠' ≟ '♢') _)
    ⟨<|>⟩
    sp-lemma s
    ⟨<|>⟩
    char-ne (λ v → return (♠ |≡| v) ⟨∧⟩ remaining s , sef-<$> _ _ (sef-rem s) , det-<$> _ _ (det-rem s) ) '♠' '(' s _ (from-dec-false ('♠' ≟ '(') _)

  round-trip (suc n)  (l ⊛ r)  s =
    let s′ = print l ++ "*" ++ print r ++ ")" ++ s
    in  ≡⟅∙⟆ (cong remaining (sym (++-assoc ("(" ++ print l) _ _ ⨾ cong (λ e → "(" ++ print l ++ e) (++-assoc ("*" ++ print r) _ _))))
             (char-ne (λ v → return (l ⊛ r |≡| v) ⟨∧⟩ remaining s , sef-<$> _ _ (sef-rem s) , det-<$> _ _ (det-rem s) ) '(' '♢' s′ (return ♢) (from-dec-false ('(' ≟ '♢') _))
        ⟨<|>⟩
        ≡⟅∙⟆ (cong remaining (sym (++-assoc ("(" ++ print l) _ _ ⨾ cong (λ e → "(" ++ print l ++ e) (++-assoc ("*" ++ print r) _ _))))
             (char-ne (λ v → return (l ⊛ r |≡| v) ⟨∧⟩ remaining s , sef-<$> _ _ (sef-rem s) , det-<$> _ _ (det-rem s) ) '(' '♠' s′ (return ♠) (from-dec-false ('(' ≟ '♠') _))
        ⟨<|>⟩
        tr-lemma n l r s
