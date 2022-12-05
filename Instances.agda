module Instances where

open import Data.Nat
import Data.Nat.Literals as Nat
open import Data.Fin
import Data.Fin.Literals as Fin
open import Data.Unit
open import Agda.Builtin.FromNat public
open import Relation.Binary.PropositionalEquality

-- Why do I have to wire these up into an instance block myself?  What am I missing?
instance
  finNumber : ∀ {n} → Number (Fin n)
  finNumber {n} = Fin.number n

  natNumber : Number ℕ
  natNumber = Nat.number

  top : ⊤
  top = _

  eq : ∀ {A : Set} {x : A} → x ≡ x
  eq = refl
