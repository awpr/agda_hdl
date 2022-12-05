module Experiments.BinaryPositive where

import Data.Nat as ℕ
open import Data.Nat using (ℕ; zero)
import Data.Nat.Properties as ℕ using (+-comm; +-assoc; +-suc; *-distribʳ-+; +-identityʳ)
open import Agda.Builtin.FromNat using (Number; fromNat)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Product using (Σ; _,_ ; Σ-syntax)

open import Data.Bit using (Bit; zero; one; not; bitToNat; _⊕_; _∧_)
open import Data.Bit.Properties using (∧-comm; ⊕-comm)
open import Instances

data Bin⁺ : Set where
  one : Bin⁺
  _+2_ : Bit -> Bin⁺ -> Bin⁺

sucIfℕ : Bit -> ℕ -> ℕ
sucIfℕ b x = bitToNat b ℕ.+ x

module ℕ⁺ where
  record ℕ⁺ : Set where
    constructor suc
    field
      pred : ℕ

  open ℕ⁺ using (pred) public

  suc⁺ : ℕ⁺ → ℕ⁺
  suc⁺ (suc n) = suc (ℕ.suc n)

  sucIf : Bit -> ℕ⁺ -> ℕ⁺
  sucIf b (suc n) = suc (sucIfℕ b n)

  toNat : ℕ⁺ -> ℕ
  toNat (suc n) = ℕ.suc n

  _+_ : ℕ⁺ -> ℕ⁺ -> ℕ⁺
  suc x + y = suc (x ℕ.+ (toNat y))

open ℕ⁺ using (ℕ⁺; sucIf)

twice : ℕ⁺ -> ℕ⁺
twice (ℕ⁺.suc n) = ℕ⁺.suc (ℕ.suc (n ℕ.* 2))

bin⁺ToNat⁺ : Bin⁺ -> ℕ⁺
bin⁺ToNat⁺ one = ℕ⁺.suc 0
bin⁺ToNat⁺ (b +2 x) = sucIf b (twice (bin⁺ToNat⁺ x))

bin⁺ToNat : Bin⁺ -> ℕ
bin⁺ToNat b = ℕ⁺.toNat (bin⁺ToNat⁺ b)

suc⁺ : Bin⁺ -> Bin⁺
suc⁺ one = zero +2 one
suc⁺ (zero +2 x) = one +2 x
suc⁺ (one +2 x) = zero +2 suc⁺ x

natSucToBin⁺ : ℕ -> Bin⁺
natSucToBin⁺ ℕ.zero = one
natSucToBin⁺ (ℕ.suc n) = suc⁺ (natSucToBin⁺ n)

nat⁺ToBin⁺ : ℕ⁺ -> Bin⁺
nat⁺ToBin⁺ (ℕ⁺.suc n) = natSucToBin⁺ n

lem-bin⁺ToNat-suc⁺ : (x : Bin⁺) -> bin⁺ToNat⁺ (suc⁺ x) ≡ ℕ⁺.suc⁺ (bin⁺ToNat⁺ x)
lem-bin⁺ToNat-suc⁺ one = refl
lem-bin⁺ToNat-suc⁺ (zero +2 x) = refl
lem-bin⁺ToNat-suc⁺ (one +2 x) rewrite lem-bin⁺ToNat-suc⁺ x = refl

lem-nat⁺ToBin⁺-iso : ∀ n -> bin⁺ToNat⁺ (nat⁺ToBin⁺ n) ≡ n
lem-nat⁺ToBin⁺-iso (ℕ⁺.suc ℕ.zero) = refl
lem-nat⁺ToBin⁺-iso (ℕ⁺.suc (ℕ.suc n))
  rewrite lem-bin⁺ToNat-suc⁺ (natSucToBin⁺ n)
  rewrite lem-nat⁺ToBin⁺-iso (ℕ⁺.suc n)
  = refl

lem-nat⁺ToBin⁺-+2
  : ∀ b n
  -> nat⁺ToBin⁺ (sucIf b (twice (ℕ⁺.suc n))) ≡ b +2 (nat⁺ToBin⁺ (ℕ⁺.suc n))
lem-nat⁺ToBin⁺-+2 zero zero = refl
lem-nat⁺ToBin⁺-+2 zero (ℕ.suc n) rewrite lem-nat⁺ToBin⁺-+2 zero n = refl
lem-nat⁺ToBin⁺-+2 one zero = refl
lem-nat⁺ToBin⁺-+2 one (ℕ.suc n) rewrite lem-nat⁺ToBin⁺-+2 one n = refl

lem-bin⁺ToNat⁺-iso : ∀ x -> nat⁺ToBin⁺ (bin⁺ToNat⁺ x) ≡ x
lem-bin⁺ToNat⁺-iso one = refl
lem-bin⁺ToNat⁺-iso (b +2 x)
  rewrite lem-nat⁺ToBin⁺-+2 b (ℕ⁺.pred (bin⁺ToNat⁺ x))
  rewrite lem-bin⁺ToNat⁺-iso x
  = refl

instance
  number : Number Bin⁺
  Number.Constraint number n = Σ[ pn ∈ ℕ ] (n ≡ ℕ.suc pn)
  Number.fromNat number .(ℕ.suc pn) {{pn , refl}} = nat⁺ToBin⁺ (ℕ⁺.suc pn)

  isSuc : ∀ {n} -> Σ[ pn ∈ ℕ ] (ℕ.suc n ≡ ℕ.suc pn)
  isSuc {n} = n , refl

carry : Bit -> Bin⁺ -> Bin⁺
carry zero x = x
carry one x = suc⁺ x

lem-carry-correct : ∀ b x -> bin⁺ToNat⁺ (carry b x) ≡ sucIf b (bin⁺ToNat⁺ x)
lem-carry-correct zero x = refl
lem-carry-correct one x rewrite lem-bin⁺ToNat-suc⁺ x = refl

_+_ : Bin⁺ -> Bin⁺ -> Bin⁺
one + x = suc⁺ x
x + one = suc⁺ x
(b +2 x) + (b₁ +2 x₁) = (b ⊕ b₁) +2 carry (b ∧ b₁) (x + x₁)

lem-sucIfℕ-suc : ∀ b n -> sucIfℕ b (ℕ.suc n) ≡ ℕ.suc (sucIfℕ b n)
lem-sucIfℕ-suc zero n = refl
lem-sucIfℕ-suc one n = refl

lem-+-correct : ∀ x y -> bin⁺ToNat (x + y) ≡ bin⁺ToNat x ℕ.+ bin⁺ToNat y
lem-+-correct one one = refl
lem-+-correct one (zero +2 x) rewrite lem-carry-correct zero x = refl
lem-+-correct one (one +2 x) rewrite lem-carry-correct one x = refl
lem-+-correct (zero +2 x) one
  rewrite ℕ.+-comm (ℕ⁺.pred (bin⁺ToNat⁺ x) ℕ.* 2) 1
  rewrite lem-carry-correct zero x
  = refl
lem-+-correct (one +2 x) one
  rewrite ℕ.+-comm (ℕ⁺.pred (bin⁺ToNat⁺ x) ℕ.* 2) 1
  rewrite lem-carry-correct one x
  = refl
lem-+-correct (zero +2 x₁) (zero +2 x₂)
  rewrite cong (ℕ._* 2) (lem-+-correct x₁ x₂)
  rewrite ℕ.*-distribʳ-+ 2 (bin⁺ToNat x₁) (bin⁺ToNat x₂)
  = refl
lem-+-correct (one +2 x₁) (zero +2 x₂)
  rewrite cong (ℕ._* 2) (lem-+-correct x₁ x₂)
  rewrite ℕ.*-distribʳ-+ 2 (bin⁺ToNat x₁) (bin⁺ToNat x₂)
  = refl
lem-+-correct (zero +2 x₁) (one +2 x₂)
  rewrite cong (ℕ._* 2) (lem-+-correct x₁ x₂)
  rewrite ℕ.*-distribʳ-+ 2 (bin⁺ToNat x₁) (bin⁺ToNat x₂)
  rewrite ℕ.+-suc (ℕ⁺.pred (bin⁺ToNat⁺ x₁) ℕ.* 2) (ℕ.suc (ℕ.suc (ℕ⁺.pred (bin⁺ToNat⁺ x₂) ℕ.* 2)))
  = refl
lem-+-correct (one +2 x₁) (one +2 x₂)
  rewrite lem-bin⁺ToNat-suc⁺ (x₁ + x₂)
  rewrite cong (ℕ._* 2) (lem-+-correct x₁ x₂)
  rewrite ℕ.*-distribʳ-+ 2 (bin⁺ToNat x₁) (bin⁺ToNat x₂)
  rewrite ℕ.+-suc (ℕ⁺.pred (bin⁺ToNat⁺ x₁) ℕ.* 2) (ℕ.suc (ℕ.suc (ℕ⁺.pred (bin⁺ToNat⁺ x₂) ℕ.* 2)))
  = refl

lem-bin⁺ToNat⁺-carry : ∀ b x -> bin⁺ToNat⁺ (carry b x) ≡ ℕ⁺.sucIf b (bin⁺ToNat⁺ x)
lem-bin⁺ToNat⁺-carry zero x = refl
lem-bin⁺ToNat⁺-carry one x rewrite lem-bin⁺ToNat-suc⁺ x = refl

lem-sucIfℕ-* : ∀ b n k -> sucIfℕ b n ℕ.* k ≡ (sucIfℕ b 0 ℕ.* k) ℕ.+ (n ℕ.* k)
lem-sucIfℕ-* zero n k = refl
lem-sucIfℕ-* one n k rewrite ℕ.+-identityʳ k = refl

lem-&&-^-bitToNat : ∀ b c -> bitToNat (b ⊕ c) ℕ.+ bitToNat (b ∧ c) ℕ.* 2 ≡ bitToNat b ℕ.+ bitToNat c
lem-&&-^-bitToNat zero zero = refl
lem-&&-^-bitToNat zero one = refl
lem-&&-^-bitToNat one zero = refl
lem-&&-^-bitToNat one one = refl

lem-+-correct2 : ∀ x y -> bin⁺ToNat⁺ (x + y) ≡ bin⁺ToNat⁺ x ℕ⁺.+ bin⁺ToNat⁺ y
lem-+-correct2 one one = refl
lem-+-correct2 one (zero +2 x) = refl
lem-+-correct2 one (one +2 x) rewrite lem-bin⁺ToNat-suc⁺ x = refl
lem-+-correct2 (zero +2 x) one
  rewrite ℕ.+-comm (ℕ⁺.pred (bin⁺ToNat⁺ x) ℕ.* 2) 1
  = refl
lem-+-correct2 (one +2 x) one
  rewrite ℕ.+-comm (ℕ⁺.pred (bin⁺ToNat⁺ x) ℕ.* 2) 1
  rewrite lem-bin⁺ToNat-suc⁺ x
  = refl
lem-+-correct2 (b₁ +2 x₁) (b₂ +2 x₂)
  rewrite lem-bin⁺ToNat⁺-carry (b₁ ∧ b₂) (x₁ + x₂)
  rewrite lem-+-correct2 x₁ x₂
  with ℕ⁺.suc n₁ <- bin⁺ToNat⁺ x₁
  with ℕ⁺.suc n₂ <- bin⁺ToNat⁺ x₂
  rewrite ℕ.+-suc n₁ n₂
  rewrite ℕ.*-distribʳ-+ 2 (bitToNat (b₁ ∧ b₂)) (ℕ.suc (n₁ ℕ.+ n₂))
  rewrite ℕ.*-distribʳ-+ 2 n₁ n₂
  with 2n₁ <- n₁ ℕ.* 2
  with 2n₂ <- n₂ ℕ.* 2
  rewrite ℕ.+-suc (bitToNat (b₁ ⊕ b₂)) (bitToNat (b₁ ∧ b₂) ℕ.* 2 ℕ.+ (2 ℕ.+ (2n₁ ℕ.+ 2n₂)))
  rewrite sym (ℕ.+-assoc (bitToNat (b₁ ⊕ b₂)) (bitToNat (b₁ ∧ b₂) ℕ.* 2) (2 ℕ.+ (2n₁ ℕ.+ 2n₂)))
  rewrite lem-&&-^-bitToNat b₁ b₂
  with b₁ <- bitToNat b₁
  with b₂ <- bitToNat b₂
  rewrite ℕ.+-suc b₂ 2n₂
  rewrite ℕ.+-suc b₁ 2n₁
  rewrite ℕ.+-suc (b₁ ℕ.+ 2n₁) (ℕ.suc (b₂ ℕ.+ 2n₂))
  rewrite ℕ.+-suc (b₁ ℕ.+ 2n₁) (b₂ ℕ.+ 2n₂)
  rewrite ℕ.+-suc (b₁ ℕ.+ b₂) (ℕ.suc (2n₁ ℕ.+ 2n₂))
  rewrite ℕ.+-suc (b₁ ℕ.+ b₂) (2n₁ ℕ.+ 2n₂)
  rewrite sym (ℕ.+-assoc (b₁ ℕ.+ b₂) 2n₁ 2n₂)
  rewrite sym (ℕ.+-assoc (b₁ ℕ.+ 2n₁) b₂ 2n₂)
  rewrite ℕ.+-assoc b₁ b₂ 2n₁
  rewrite ℕ.+-assoc b₁ 2n₁ b₂
  rewrite ℕ.+-comm b₂ 2n₁
  -- lol, that's a _lot_ of manually-typed algebraic manipulation...
  = refl

+-comm : ∀ x y -> x + y ≡ y + x
+-comm one one = refl
+-comm one (b +2 x) = refl
+-comm (b +2 x) one = refl
+-comm (b₁ +2 x₁) (b₂ +2 x₂)
  rewrite ∧-comm b₁ b₂
  rewrite ⊕-comm b₁ b₂
  rewrite +-comm x₁ x₂ = refl

+-assoc : ∀ x y z -> x + (y + z) ≡ (x + y) + z
+-assoc x y z
  rewrite sym (lem-bin⁺ToNat⁺-iso (x + (y + z)))
  rewrite lem-+-correct2 x (y + z)
  rewrite lem-+-correct2 y z
  rewrite sym (lem-bin⁺ToNat⁺-iso ((x + y) + z))
  rewrite lem-+-correct2 (x + y) z
  rewrite lem-+-correct2 x y
  with ℕ⁺.suc x <- bin⁺ToNat⁺ x
  with ℕ⁺.suc y <- bin⁺ToNat⁺ y
  with ℕ⁺.suc z <- bin⁺ToNat⁺ z
  rewrite ℕ.+-assoc x (1 ℕ.+ y) (1 ℕ.+ z)
  = refl

{-
+-assoc one one one = refl
+-assoc one one (zero +2 z) = refl
+-assoc one one (one +2 z) = refl
+-assoc one (zero +2 y) one = refl
+-assoc one (zero +2 y) (zero +2 z) = refl
+-assoc one (zero +2 y) (one +2 z) = refl
+-assoc one (one +2 y) one = refl
+-assoc one (one +2 y) (zero +2 z) rewrite +-assoc 1 y z = refl
+-assoc one (one +2 y) (one +2 z) rewrite +-assoc 1 y z = refl
+-assoc (x +2 x₁) y z = {!!}
-}
