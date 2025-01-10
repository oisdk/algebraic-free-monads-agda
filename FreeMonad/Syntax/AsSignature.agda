{-# OPTIONS --safe #-}

open import Signatures
open import Prelude

module FreeMonad.Syntax.AsSignature (𝔽 : Signature) where

open import FreeMonad.Syntax 𝔽
open Signature 𝔽

Position : Syntax A → Type
Position (var _) = ⊤
Position (op (Oᵢ , k)) = Σ[ i ⦂ Arity Oᵢ ] × Position (k i)

★ : Signature
★ = Syntax ⊤ ◁ Position

open SyntaxBind using (_<$>_; _>>=_)

shape : Syntax A → Syntax ⊤
shape t = const tt <$> t

Index : Syntax A → Type
Index = Position ∘ shape

lookup : (s : Syntax A) → Index s → A
lookup (var x)       _         = x
lookup (op (O , k))  (i , is)  = lookup (k i) is

fill : (s : Syntax A) → (Position s → B) → Syntax B
fill (var x)       i = var (i tt)
fill (op (O , k))  i = op (O , λ j → fill (k j) (i ∘ _,_ j))

⟦op⟧ : ⟦ 𝔽 ⟧ (⟦ ★ ⟧ A) → ⟦ ★ ⟧ A
⟦op⟧ (S , P) = op (S , fst ∘ P) , uncurry (snd ∘′ P)

Indexed : Syntax A ⇔ ⟦ ★ ⟧ A
Indexed .fun s = shape s , lookup s
Indexed .inv = uncurry fill
Indexed .leftInv =
  elim-s _ λ { (var x) → refl ; (op (O , k) P⟨xs⟩) → cong (op ∘ _,_ O) (funExt P⟨xs⟩) }
Indexed .rightInv = uncurry (elim-s _ λ { (var x) P → refl ; (op (O , k) P⟨xs⟩) P → cong (⟦op⟧ ∘ _,_ O) (funExt λ i → P⟨xs⟩ i _) })

<$>⇔cmap : (f : A → B) (s : Syntax A) → f <$> s ≡ Indexed .inv (cmap f (Indexed .fun s))
<$>⇔cmap f = elim-s _ λ { (var x) → refl ; (op (O , k) P⟨xs⟩) → cong (op ∘ _,_ O) (funExt P⟨xs⟩) }

<$>-com-inv : (f : A → B) (s : ⟦ ★ ⟧ A) → f <$> Indexed .inv s ≡ Indexed .inv (cmap f s)
<$>-com-inv f s = <$>⇔cmap f (Indexed .inv s) ⨾ cong (Indexed .inv ∘ cmap f) (Indexed .rightInv s)

module _ (f : A → B) (s : Syntax A) where
  <$>-com-fun : cmap f (Indexed .fun s) ≡ Indexed .fun (f <$> s)
  <$>-com-fun = sym (cong (Indexed .fun) (<$>⇔cmap f s) ⨾ Indexed .rightInv (cmap f (Indexed .fun s)))

  <$>-same-shape :  shape s ≡ shape (f <$> s)
  <$>-same-shape = PathPΣ <$>-com-fun .fst

  <$>-lookup : ∀ i → lookup (f <$> s) i ≡ f (lookup s (subst Position (sym <$>-same-shape) i))
  <$>-lookup i = sym (cong (_$ i) (fromPathP (PathPΣ <$>-com-fun .snd))) ⨾ transportRefl _

open import Isomorphism.Properties

infixr 5 _∈_ _∉_
_∈_ : A → Syntax A → Type _
x ∈ xs = Fibre (lookup xs) x

_∉_ : A → Syntax A → Type _
x ∉ xs = ¬ (x ∈ xs)

open import Data.Sigma.Properties

module _ (disc : ∀ Oᵢ → Discrete (Signature.Arity 𝔽 Oᵢ)) where
  disc-index : (s : Syntax A) → Discrete (Index s)
  disc-index =
    elim-s _ λ { (var v) _ _ → yes refl
               ; (op (O , k) P⟨xs⟩) → discreteΣ (disc O) P⟨xs⟩ }

open SyntaxBind

>>=-ind : Syntax A → (A → Syntax B) → Type
>>=-ind xs k = Index (xs >>= k)

>>=∙-ind : Syntax A → (A → Syntax B) → Type
>>=∙-ind xs k = Σ[ i ⦂ Index xs ] × Index (k (lookup xs i))

lookup∙ : (xs : Syntax A) (k : A → Syntax B) → >>=∙-ind xs k → B
lookup∙ xs k = uncurry (lookup ∘′ k ∘′ lookup xs)

module _ (k : A → Syntax B) where
  pull-shape : (s : Syntax A) → >>=-ind s k → >>=∙-ind s k
  pull-shape = elim-s _ λ { (var x) i → tt , i ; (op (O , k) P⟨xs⟩) (i , is) → let j , js = P⟨xs⟩ i is in (i , j) , js }

  push-shape : (s : Syntax A) → >>=∙-ind s k → >>=-ind s k
  push-shape = elim-s _ λ { (var x) (i , is) → is ; (op (O , k) P⟨xs⟩) ((i , is) , js) → i , P⟨xs⟩ i (is , js) }

  push∘pull : (s : Syntax A) (i : >>=-ind s k) → push-shape s (pull-shape s i) ≡ i
  push∘pull = elim-s _ λ { (var x) _ → refl ; (op (O , k) P⟨xs⟩) (i , is) → cong (i ,_) (P⟨xs⟩ i is) }

  pull∘push : (s : Syntax A) (i : >>=∙-ind s k) → pull-shape s (push-shape s i) ≡ i
  pull∘push =
    elim-s _ λ { (var x) _ → refl
               ; (op (O , k) P⟨xs⟩) ((i , is) , js) p →  let (j′ , js′) = P⟨xs⟩ i (is , js) p in ((i , j′) , js′) }

  lookup-push : (s : Syntax A) (i : Index s) (is : Index (k (lookup s i))) → lookup (k (lookup s i)) is ≡ lookup (s >>= k) (push-shape s (i , is))
  lookup-push = elim-s _ λ { (var x) i is → refl
                           ; (op (O , k) P⟨xs⟩) (i , is′) is → P⟨xs⟩ i is′ is
                           }

  lookup-pull : (s : Syntax A) (i : Index (s >>= k)) → uncurry (lookup ∘′ k ∘′ lookup s) (pull-shape s i) ≡ lookup (s >>= k) i
  lookup-pull = elim-s _ λ { (var x) i → refl
                           ; (op (O , k) P⟨xs⟩) (i , is′) → P⟨xs⟩ i is′
                           }

>>=⟦⟧ :  (k : A → Syntax B) (f : ∀ x → Index (k x) → C) (xs : Syntax A)
      → Indexed .inv (shape (xs >>= k) , uncurry (f ∘′ lookup xs) ∘ pull-shape k xs) ≡ xs >>= fill _ ∘′ f
>>=⟦⟧ k f = elim-s _
  λ { (var x) → refl ; (op (O , _) P⟨xs⟩) → cong (op ∘ _,_ O) (funExt P⟨xs⟩) }
