module Experiments.BinaryIndexed where

import Data.Nat
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
import Data.Nat as ℕ using (zero; suc; _+_; _*_)
open import Data.Product using (Σ; _,_; Σ-syntax)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; [_]; cong)
open import Agda.Builtin.FromNat using (Number; fromNat)

open import Data.Bit
open import Instances

open Number using (Constraint)

infixr 40 _+2_
data Bin : Bit -> Set where
  ∅ : Bin 0
  _+2_ : ∀ {b₀} -> (b : Bit) -> Bin (not b) -> Bin b₀

example3 : Bin 0
example3 = ∅

example4 : Bin 0
example4 = 1 +2 1 +2 0 +2 1 +2 ∅

binToNat : ∀ {b} -> Bin b -> ℕ
binToNat ∅ = 0
binToNat (b +2 x) = bitToNat b ℕ.+ binToNat x ℕ.* 2

z : ∀ {b} -> Bin b -> Bin 0
z ∅ = ∅
z (b +2 x) = b +2 x

lem-z-identity : ∀ b -> z b ≡ b
lem-z-identity ∅ = refl
lem-z-identity (b +2 b₁) = refl

lem-z-binToNat : (b : Bin 1) -> binToNat (z b) ≡ binToNat b
lem-z-binToNat (b +2 b₁) = refl

nz : ∀ {b} -> Bin 1 -> Bin b
nz (b +2 x) = b +2 x

suc : ∀ {z w} -> Bin z -> Bin w
suc ∅ = 1 +2 ∅
suc (zero +2 x) = 1 +2 z x
suc (one +2 x) = 0 +2 suc x

natToBin : ℕ -> Bin 0
natToBin ℕ.zero = ∅
natToBin (ℕ.suc n) = suc (natToBin n)

natToBinSuc : ∀ {z} -> ℕ -> Bin z
natToBinSuc n = suc (natToBin n)

lem-natToBin-0 : ∀ n -> natToBin n ≡ ∅ -> n ≡ 0
lem-natToBin-0 ℕ.zero eq = refl
lem-natToBin-0 (ℕ.suc n) eq with natToBin n
lem-natToBin-0 (ℕ.suc n) () | zero +2 x
lem-natToBin-0 (ℕ.suc n) () | one +2 x

lem-binToNat-suc : ∀ {z w} (x : Bin z) -> binToNat (suc {z} {w} x) ≡ ℕ.suc (binToNat x)
lem-binToNat-suc ∅ = refl
lem-binToNat-suc (zero +2 x) rewrite lem-z-binToNat x = refl
lem-binToNat-suc (one +2 x) rewrite lem-binToNat-suc {0} {1} x = refl

lem-natToBin-iso : ∀ n -> binToNat (natToBin n) ≡ n
lem-natToBin-iso ℕ.zero = refl
lem-natToBin-iso (ℕ.suc n)
  rewrite lem-binToNat-suc {0} {0} (natToBin n)
  rewrite lem-natToBin-iso n
  = refl

_+2'_ : ∀ {z} -> Bit -> Bin z -> Bin z
zero +2' ∅ = ∅
one +2' ∅ = 1 +2 ∅
b +2' (b₁ +2 x) = b +2 b₁ +2 x

lem-z-+2' : ∀ b x -> b +2' (z x) ≡ b +2 x
lem-z-+2' zero (b +2 x) = refl
lem-z-+2' one ∅ = refl
lem-z-+2' one (b +2 x) = refl

-- N.B. even though I set out to fix the problem of needing to
-- distinguish 1 from other odd numbers in the outermost constructor,
-- this representation now has the same problem for 0/evens, on top of
-- having the extra often-invisible parameter to Bin.  So does that
-- mean it's actually made things worse?
lem-natToBin-+2' : ∀ b n -> natToBin (bitToNat b ℕ.+ n ℕ.* 2) ≡ b +2' natToBin n
lem-natToBin-+2' zero ℕ.zero = refl
lem-natToBin-+2' one ℕ.zero = refl
lem-natToBin-+2' zero (ℕ.suc n) rewrite lem-natToBin-+2' zero n with natToBin n
... | ∅ = refl
... | one +2 x = refl
... | zero +2 x = refl
lem-natToBin-+2' one (ℕ.suc n) rewrite lem-natToBin-+2' one n with natToBin n
... | ∅ = refl
... | one +2 x = refl
... | zero +2 x = refl

lem-binToNat-iso : ∀ {w} (x : Bin w) -> natToBin (binToNat x) ≡ z x
lem-binToNat-iso ∅ = refl
lem-binToNat-iso (b +2 x)
  rewrite lem-natToBin-+2' b (binToNat x)
  rewrite lem-binToNat-iso x
  rewrite lem-z-+2' b x
  = refl
