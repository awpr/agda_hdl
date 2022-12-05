module Experiments.FixedBinary where

import Data.Nat
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
import Data.Nat as ℕ using (zero; suc; _+_; _*_)
open import Data.Nat.Literals using (number)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; _∷_; []; map; replicate; _++_; last)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; [_]; cong)

open import Experiments.Binary using (Bin)
open import Data.Bit
open import Instances

record UInt (n : ℕ) : Set where
  constructor MkInt
  field
    repr : Vec Bit n -- LSB first

record Int (n : ℕ) : Set where
  constructor MkInt
  field
    repr : Vec Bit n -- LSB first

infix 40 _#_
pattern _#_ n x = MkInt {n} x

infix 60 _₀ _₁
pattern _₀ n = zero ∷ n
pattern _₁ n = one ∷ n

_ : UInt 4
_ = 4 # [] ₀ ₁ ₀ ₁

toℕ′ : ∀ {n} → Vec Bit n → ℕ
toℕ′ [] = 0
toℕ′ (n ₀) = toℕ′ n ℕ.* 2
toℕ′ (n ₁) = 1 ℕ.+ toℕ′ n ℕ.* 2

twoOf : (x y z : Bit) → Bit
twoOf x y z = x ∧ y ∨ y ∧ z ∨ z ∧ x

add : ∀ {n} → Bit → (x y : Vec Bit n) → Bit × Vec Bit n
add c [] [] = c , []
add c (x ∷ xs) (y ∷ ys) with add (twoOf c x y) xs ys
... | c′ , xys = c′ , (c ⊕ x ⊕ y) ∷ xys

negate : ∀ {n} → Bit → Vec Bit n → Vec Bit n
negate c [] = []
negate c (x ∷ xs) = (not x ⊕ c) ∷ negate (not x ∧ c) xs

complement : ∀ {n} → Vec Bit n → Vec Bit n
complement = map not

ext : ∀ {m n} → Int n → Int (n ℕ.+ m)
ext (MkInt []) = MkInt (replicate 0)
ext (MkInt (b ∷ repr)) = MkInt ((b ∷ repr) ++ replicate (last (b ∷ repr)))

_+_ _-_ : ∀ {n} (x y : Int n) → Int n
x + y = MkInt (proj₂ (add 0 (Int.repr x) (Int.repr y)))

x - y = MkInt (proj₂ (add 1 (Int.repr x) (complement (Int.repr y))))
