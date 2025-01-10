{-# OPTIONS --safe #-}

module Data.String where

open import Agda.Builtin.Char using (Char) public
open import Agda.Builtin.String using (primStringToList) public
open import Data.List using (List)
open import Level using (Type)

String : Type
String = List Char

{-# BUILTIN FROMSTRING primStringToList #-}

_ : String
_ = "hello"
