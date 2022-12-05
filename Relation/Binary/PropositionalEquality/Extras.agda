{-# OPTIONS --safe #-}

module Relation.Binary.PropositionalEquality.Extras where

open import Function using (id)

open import Relation.Binary.PropositionalEquality public

cast : ∀ {a} {A : Set a} {B : Set a} → A ≡ B → A → B
cast = subst id


