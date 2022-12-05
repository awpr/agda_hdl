module Experiments.Binary where

import Data.Nat as ℕ
open import Data.Nat as ℕ using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Experiments.BinaryPositive as Bin⁺
open import Experiments.BinaryPositive using
  ( Bin⁺; one; _+2_; bin⁺ToNat; bin⁺ToNat⁺; nat⁺ToBin⁺; module ℕ⁺; suc⁺
  ; lem-bin⁺ToNat⁺-iso; lem-nat⁺ToBin⁺-iso
  )
open import Data.Bit

data Bin : Set where
  zero : Bin
  pos : Bin⁺ -> Bin

binToNat : Bin -> ℕ
binToNat zero = ℕ.zero
binToNat (pos n) = bin⁺ToNat n

natToBin : ℕ -> Bin
natToBin ℕ.zero = zero
natToBin (ℕ.suc n) = pos (nat⁺ToBin⁺ (ℕ⁺.suc n))

lem-ℕ⁺-suc-pred : ∀ n -> ℕ⁺.suc (ℕ⁺.pred n) ≡ n
lem-ℕ⁺-suc-pred (ℕ⁺.suc x) = refl

lem-binToNat-iso : ∀ x -> natToBin (binToNat x) ≡ x
lem-binToNat-iso zero = refl
lem-binToNat-iso (pos x)
  rewrite lem-ℕ⁺-suc-pred (bin⁺ToNat⁺ x)
  rewrite lem-bin⁺ToNat⁺-iso x
  = refl

lem-natToBin-iso : ∀ n -> binToNat (natToBin n) ≡ n
lem-natToBin-iso ℕ.zero = refl
lem-natToBin-iso (ℕ.suc n)
  rewrite lem-ℕ⁺-suc-pred (ℕ⁺.suc n)
  rewrite lem-nat⁺ToBin⁺-iso (ℕ⁺.suc n)
  = refl

one+2 : Bin -> Bin⁺
one+2 zero = one
one+2 (pos y) = one +2 y

pred : Bin⁺ -> Bin
pred one = zero
pred (b +2 x) = pos (result b)
 where
  result : Bit -> Bin⁺
  result one = zero +2 x
  result zero = one+2 (pred x)

suc⁰ : Bin -> Bin⁺
suc⁰ zero = one
suc⁰ (pos n) = suc⁺ n

suc : Bin -> Bin
suc b = pos (suc⁰ b)

lem-suc-one+2 : ∀ n -> suc⁺ (one+2 n) ≡ zero +2 suc⁰ n
lem-suc-one+2 zero = refl
lem-suc-one+2 (pos one) = refl
lem-suc-one+2 (pos (x +2 x₁)) = refl

lem-suc-pred : ∀ n -> suc⁰ (pred n) ≡ n
lem-suc-pred one = refl
lem-suc-pred (one +2 n) = refl
lem-suc-pred (zero +2 n) with n
... | one = refl
... | one +2 x = refl
... | zero +2 x
  rewrite lem-suc-one+2 (pred (zero +2 x))
  rewrite lem-suc-one+2 (pred x)
  rewrite lem-suc-pred x
    = refl

_+_ : Bin -> Bin -> Bin
zero + zero = zero
zero + pos x = pos x
pos x + zero = pos x
pos x + pos y = pos (x Bin⁺.+ y)
