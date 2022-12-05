open import Categories.Distributive using (DistributiveCategory)

module Circuits.Compressor {o m ℓ} (𝓒 : DistributiveCategory o m ℓ) where

open import Data.Nat using (suc; zero)

open import Categories.Gel.Distributive 𝓒
open import Categories.Gel.Product (DistributiveCategory.cartesianCategory 𝓒)
open import Categories.Gel.Vec (DistributiveCategory.cartesianCategory 𝓒)
open import Circuits.Bit 𝓒
open import Circuits.Binary 𝓒

open DoNotation

compressCell4to2 : Bit ⟶ Bit ⇨ Bit ⇨ Bit ⇨ Bit ⇨ Bit × Bit × Bit
compressCell4to2 a b c d cix = do
  abc ← fullAdder a b c
  abcdc ← fullAdder (snd abc) (! d) (! cix)
  fst abc , fst abcdc , snd abcdc

compress4to2′
  : ∀ {n}
  → Vec Bit n
  ⟶ Vec Bit n
  ⇨ Vec Bit n
  ⇨ Vec Bit n
  ⇨ Bit × Vec Bit n × Vec Bit (suc n)
compress4to2′ {zero} _ _ _ _ = false , [] , (false ∷ [])
compress4to2′ {suc n} x y z w = do
  tl ← compress4to2′ (tail x) (tail y) (tail z) (tail w)
  hd ← compressCell4to2 (! head x) (! head y) (! head z) (! head w) (fst tl)
  let s,co = snd tl
  fst hd , (snd (snd hd) ∷ fst s,co) , (fst (snd hd) ∷ snd s,co)

-- Vec order: MSB first
compress4to2
  : ∀ {n}
  → UInt n ⟶ UInt n ⇨ UInt n ⇨ UInt n ⇨ UInt n × UInt n
compress4to2 x y z w = do
  x′ ← bits x
  y′ ← ! bits y
  z′ ← ! bits z
  w′ ← ! bits w
  r ← snd (compress4to2′ x′ y′ z′ w′)
  -- N.B. type inference has been fragile around here, but seemingly
  -- the `uint` constructor gave it enough of a hint to work; see
  -- commit history immediately before this comment was introduced
  -- for more details.
  uint (fst r) , uint (tail (snd r))
