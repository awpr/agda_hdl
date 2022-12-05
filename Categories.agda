{-# OPTIONS --safe #-}

module Categories where

open import Agda.Builtin.Reflection using (withReconstructed)
open import Agda.Primitive using (Setω)

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.List as List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe; fromMaybe; _<∣>_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Show as ℕ
import Data.Product as Product -- using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.String as String using (String)
open import Data.Unit using (⊤; tt)
open import Function using (_$_; it)
open import Level using (Level; Lift; lift; _⊔_)
open import Reflection.DeBruijn using (η-expand; weaken; strengthenBy)
open import Reflection.Term
open import Reflection.Abstraction
open import Reflection.Argument
open import Reflection.Argument.Visibility
open import Reflection.Show
open import Reflection.TypeChecking.Monad
open import Reflection.TypeChecking.Monad.Syntax
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Braided public
open import Categories.Cartesian public
open import Categories.CartesianClosed public
open import Categories.Category public
open import Categories.Category.Types public
open import Categories.Functor public
open import Categories.Monoidal public
open import Categories.Terminal public
