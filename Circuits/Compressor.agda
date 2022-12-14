open import Categories.Distributive using (DistributiveCategory)

module Circuits.Compressor {o m ā} (š : DistributiveCategory o m ā) where

open import Data.Nat using (suc; zero)

open import Categories.Gel.Distributive š
open import Categories.Gel.Product (DistributiveCategory.cartesianCategory š)
open import Categories.Gel.Vec (DistributiveCategory.cartesianCategory š)
open import Circuits.Bit š
open import Circuits.Binary š

open DoNotation

compressCell4to2 : Bit ā¶ Bit āØ Bit āØ Bit āØ Bit āØ Bit Ć Bit Ć Bit
compressCell4to2 a b c d cix = do
  abc ā fullAdder a b c
  abcdc ā fullAdder (snd abc) (! d) (! cix)
  fst abc , fst abcdc , snd abcdc

compress4to2ā²
  : ā {n}
  ā Vec Bit n
  ā¶ Vec Bit n
  āØ Vec Bit n
  āØ Vec Bit n
  āØ Bit Ć Vec Bit n Ć Vec Bit (suc n)
compress4to2ā² {zero} _ _ _ _ = false , [] , (false ā· [])
compress4to2ā² {suc n} x y z w = do
  tl ā compress4to2ā² (tail x) (tail y) (tail z) (tail w)
  hd ā compressCell4to2 (! head x) (! head y) (! head z) (! head w) (fst tl)
  let s,co = snd tl
  fst hd , (snd (snd hd) ā· fst s,co) , (fst (snd hd) ā· snd s,co)

-- Vec order: MSB first
compress4to2
  : ā {n}
  ā UInt n ā¶ UInt n āØ UInt n āØ UInt n āØ UInt n Ć UInt n
compress4to2 x y z w = do
  xā² ā bits x
  yā² ā ! bits y
  zā² ā ! bits z
  wā² ā ! bits w
  r ā snd (compress4to2ā² xā² yā² zā² wā²)
  -- N.B. type inference has been fragile around here, but seemingly
  -- the `uint` constructor gave it enough of a hint to work; see
  -- commit history immediately before this comment was introduced
  -- for more details.
  uint (fst r) , uint (tail (snd r))
