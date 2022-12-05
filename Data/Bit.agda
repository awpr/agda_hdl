module Data.Bit where

-- A boolean truth value type with a digital logic flavor.
--
-- This is actually just a renaming of Data.Bool, so you can use both
-- naming schemes interchangeably.  This is different from pattern
-- synonyms for zero and one: you can have multiple constructors of
-- the same name in scope, but not a pattern and a constructor.  So if
-- we tried doing this with pattern synonyms, zero would conflict with
-- ℕ.
--
-- In addition to the contents of Data.Bool, this provides conversions
-- with ℕ and an instance for literals.

open import Data.Bool public
  renaming
    ( Bool to Bit; false to zero; true to one
    ; _xor_ to infixr 5 _⊕_ -- ⊕ is \o+
    )
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Instances

instance
  bitNumber : Number Bit

  bitNumber .Number.Constraint 0 = ⊤
  bitNumber .Number.Constraint 1 = ⊤
  bitNumber .Number.Constraint _ = ⊥

  bitNumber .fromNat 0 = zero
  bitNumber .fromNat 1 = one
  bitNumber .fromNat (ℕ.suc (ℕ.suc n)) {{()}}

bitToNat : Bit -> ℕ
bitToNat zero = 0
bitToNat one = 1

data NatBit : ℕ -> Set where
  bit : (b : Bit) -> NatBit (bitToNat b)

natToBit : (n : ℕ) -> Maybe (NatBit n)
natToBit 0 = just (bit 0)
natToBit 1 = just (bit 1)
natToBit _ = nothing

-- ↑ is \u or \u-
infixl 6 _↑_
_↑_ : Bit → Bit → Bit
zero ↑ zero = one
zero ↑ one = one
one ↑ zero = one
one ↑ one = zero

↑-correct : ∀ x y → x ↑ y ≡ not (x ∧ y)
↑-correct zero zero = refl
↑-correct zero one = refl
↑-correct one zero = refl
↑-correct one one = refl
