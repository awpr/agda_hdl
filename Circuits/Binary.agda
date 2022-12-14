open import Categories.Distributive using (DistributiveCategory)

module Circuits.Binary {o m â} (ð : DistributiveCategory o m â) where

open import Data.Nat as â using (â)
import Data.Vec as Vec
import Data.Bool as Bool

open DistributiveCategory ð hiding (_Ã_)

open import Categories.Gel.Distributive ð
open import Categories.Gel.Product cartesianCategory
open import Categories.Gel.Vec cartesianCategory
open import Circuits.Bit ð

record UInt (n : â) (X : Obj) : Set m where
  constructor uint
  field
    -- Vec order: MSB first, since carry information flows LSB-to-MSB,
    -- and this results in inductive definitions that don't need to
    -- pass extra parameters to their recursive calls.
    bits : Vec Bit n X

open UInt public using (bits)

instance
  yonedaUInt : â {n} â Yoneda (UInt n)
  yonedaUInt = record
    { wrap = Î» x â record { bits = wrap x }
    ; unwrap = Î» x â unwrap (UInt.bits x)
    }

  module _ {n} where
    open Yoneda (yonedaUInt {n}) public using () renaming (presheaf to presheafUInt)

open DoNotation

zeros : â {n X} â UInt n X
zeros = uint (replicate _ zero)

literal : â {n X} â Vec.Vec Bool.Bool n â UInt n X
literal xs = uint (fromVec fromBool xs)

-- The actual implementation of an incrementer: a ripple-carry on an
-- unwrapped vector of bits.
carryâ² : (n : â) â Bit â¶ Vec Bit n â¨ Bit Ã Vec Bit n
carryâ² â.zero b _ = b , []
carryâ² (â.suc n) b xs0 = do
  xs0â² â xs0
  tl â carryâ² n (! b) (tail xs0â²)
  let c = fst tl
      xsâ² = snd tl
  and c (head xs0â²) , (xor c (head xs0â²) â· xsâ²)

-- Add a carry bit to a binary number, maintaining the same bit width
-- and returning the carry-out as a separate bit.
carry : â {n} â Bit â¶ UInt n â¨ Bit Ã UInt n
carry b x = wrap (unwrap (carryâ² _ b (UInt.bits x)))

-- Increment, returning the carry as a separate bit.
incC : â {n} â UInt n â¶ Bit Ã UInt n
incC x = carry true x

-- Increment, incorporating the carry into a wider binary number.
inc : â {n} â UInt n â¶ UInt (â.suc n)
inc x = wrap (unwrap (incC x))

-- Increment, maintaining the bit width and truncating any carry.
incT : â {n} â UInt n â¶ UInt n
incT x = snd (incC x)
