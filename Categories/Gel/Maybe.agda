open import Categories.Distributive using (DistributiveCategory)

module Categories.Gel.Maybe {o m β} (π : DistributiveCategory o m β) where

open import Level using (Level)

open import Categories.Gel.Distributive π
open DistributiveCategory π
open import Categories.Gel.Bool π using (Bool; if_then_else_)

private
  variable
    a b : Level
    A : Obj β Set a
    B : Obj β Set b

record Maybe (A : Obj β Set a) β¦ _ : Yoneda A β¦ (X : Obj) : Set m where
  field
    unwrap : β¦ Rep A β β β§ X

instance
  yonedaMaybe : β¦ _ : Yoneda A β¦ β Yoneda (Maybe A)
  yonedaMaybe = record { wrap = Ξ» x β record { unwrap = x } ; unwrap = Maybe.unwrap }

  module _ {A : Obj β Set a} β¦ _ : Yoneda A β¦ where
    open Yoneda (yonedaMaybe {A = A}) public using () renaming (presheaf to presheafMaybe)

fromMaybe : β¦ _ : Yoneda A β¦ β A βΆ Maybe A β¨ A
fromMaybe β¦ yA β¦ z mx = case unwrap mx of [ injβ x β wrap x β₯ injβ y β ! z ]
  where open Yoneda yA using (presheaf) -- Ugh.

maybe
  : β {a b} {A : Obj β Set a} {B : Obj β Set b}
      β¦ _ : Yoneda A β¦ β¦ _ : Yoneda B β¦
  β B βΆ (A β B) β¨ Maybe A β¨ B
maybe β¦ _ β¦ β¦ yB β¦ z f mx = case unwrap mx of [ injβ x β f (wrap x) β₯ injβ _ β ! z ]
  where open Yoneda yB using (presheaf)

nothing : β {a} {A : Obj β Set a} β¦ _ : Yoneda A β¦ {X} β Maybe A X
nothing = record { unwrap = injβ Ξ΅ }

just : β {a} {A : Obj β Set a} β¦ _ : Yoneda A β¦ β A βΆ Maybe A
just x = record { unwrap = injβ (unwrap x) }

justWhen : β {a} {A : Obj β Set a} β¦ _ : Yoneda A β¦ β Bool βΆ A β¨ Maybe A
justWhen b x = if b then just x else nothing
