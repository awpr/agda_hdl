open import Categories.Distributive using (DistributiveCategory)

module Circuits.Binary {o m ℓ} (𝓒 : DistributiveCategory o m ℓ) where

open import Data.Nat as ℕ using (ℕ)
import Data.Vec as Vec
import Data.Bool as Bool

open DistributiveCategory 𝓒 hiding (_×_)

open import Categories.Gel.Distributive 𝓒
open import Categories.Gel.Product cartesianCategory
open import Categories.Gel.Vec cartesianCategory
open import Circuits.Bit 𝓒

record UInt (n : ℕ) (X : Obj) : Set m where
  constructor uint
  field
    -- Vec order: MSB first, since carry information flows LSB-to-MSB,
    -- and this results in inductive definitions that don't need to
    -- pass extra parameters to their recursive calls.
    bits : Vec Bit n X

open UInt public using (bits)

instance
  yonedaUInt : ∀ {n} → Yoneda (UInt n)
  yonedaUInt = record
    { wrap = λ x → record { bits = wrap x }
    ; unwrap = λ x → unwrap (UInt.bits x)
    }

  module _ {n} where
    open Yoneda (yonedaUInt {n}) public using () renaming (presheaf to presheafUInt)

open DoNotation

zeros : ∀ {n X} → UInt n X
zeros = uint (replicate _ zero)

literal : ∀ {n X} → Vec.Vec Bool.Bool n → UInt n X
literal xs = uint (fromVec fromBool xs)

-- The actual implementation of an incrementer: a ripple-carry on an
-- unwrapped vector of bits.
carry′ : (n : ℕ) → Bit ⟶ Vec Bit n ⇨ Bit × Vec Bit n
carry′ ℕ.zero b _ = b , []
carry′ (ℕ.suc n) b xs0 = do
  xs0′ ← xs0
  tl ← carry′ n (! b) (tail xs0′)
  let c = fst tl
      xs′ = snd tl
  and c (head xs0′) , (xor c (head xs0′) ∷ xs′)

-- Add a carry bit to a binary number, maintaining the same bit width
-- and returning the carry-out as a separate bit.
carry : ∀ {n} → Bit ⟶ UInt n ⇨ Bit × UInt n
carry b x = wrap (unwrap (carry′ _ b (UInt.bits x)))

-- Increment, returning the carry as a separate bit.
incC : ∀ {n} → UInt n ⟶ Bit × UInt n
incC x = carry true x

-- Increment, incorporating the carry into a wider binary number.
inc : ∀ {n} → UInt n ⟶ UInt (ℕ.suc n)
inc x = wrap (unwrap (incC x))

-- Increment, maintaining the bit width and truncating any carry.
incT : ∀ {n} → UInt n ⟶ UInt n
incT x = snd (incC x)
