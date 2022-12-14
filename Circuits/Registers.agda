open import Categories.Distributive using (DistributiveCategory)
open import Categories.CausalLoop using (Causal)

module Circuits.Registers
  {o m ā}
  {š : DistributiveCategory o m ā}
  (Loop : Causal (DistributiveCategory.monoidalCategory š))
  where

open import Data.Nat using (ā; suc; zero)
open import Level using (Level)

open DistributiveCategory š

open import Categories.Gel.Distributive š
open import Categories.Gel.CausalLoop cartesianCategory Loop
open import Categories.Gel.Maybe š using (Maybe; fromMaybe; presheafMaybe; justWhen)
open import Categories.Gel.Product cartesianCategory
open import Categories.Gel.Vec cartesianCategory

open import Circuits.Bit š using (Bit)

private
  variable
    a b : Level
    A : Obj ā Set a
    B : Obj ā Set b

flop
  : ā¦ _ : Yoneda A ā¦
  ā A ā ā A ā¶ A
flop ā¦ yA ā¦ xā x = unfold xā (Ī» s ā s , (! x))
  where open Yoneda yA using (presheaf)

delay
  : ā¦ _ : Yoneda A ā¦
  ā ā
  ā A ā
  ā A ā¶ A
delay zero xā x = x
delay (suc n) xā x = flop xā (delay n xā x)

latest
  : ā¦ _ : Yoneda A ā¦
  ā A ā
  ā Maybe A ā¶ A
latest ā¦ yA ā¦ xā mx =
    unfold xā (Ī» s ā s , fromMaybe s (! mx))
  where open Yoneda yA using (presheaf)

flopEnable
  : ā¦ _ : Yoneda A ā¦
  ā A ā
  ā Bit ā¶ A āØ A
flopEnable xā en x = latest xā (justWhen en x)

-- Vec order: index zero is the input from one cycle ago.
belt
  : ā {n} ā¦ _ : Yoneda A ā¦
  ā A ā
  ā A ā¶ Vec A n
belt {n = zero} _ _ = []
belt {n = suc n} ā¦ yA ā¦ xā x = do
   xā² ā flop xā x
   xsā² ā belt xā xā²
   xā² ā· xsā²
 where
   open DoNotation
   open Yoneda yA using (presheaf)
