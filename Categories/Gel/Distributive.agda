open import Categories.Distributive using (DistributiveCategory)

module Categories.Gel.Distributive {o m β} (π : DistributiveCategory o m β) where

open DistributiveCategory π

import Function

import Categories.Inverse
open Categories.Inverse.In π€ using (RawInverse)
open import Categories.Gel.Cartesian cartesianCategory public
open import Categories.Gel.Coproducts cartesianCategory coproducts
  using (injβ; injβ)
  public

β-elim _β₯_
  : β {A B} {c} {C : Obj β Set c} β¦ _ : Yoneda C β¦
  β (β¦ A β§ β C) βΆ (β¦ B β§ β C) β¨ β¦ A β B β§ β¨ C
(f β₯ g) x = wrap (
  (unwrap (_β£_.unwrap (reify f)) β½ unwrap (_β£_.unwrap (reify g))) β
  distΚ³ .RawInverse.fβ»ΒΉ β (x β³ id) )

β-elim = _β₯_

syntax β-elim (Ξ» x β eβ) (Ξ» y β eβ) eβ = case eβ of [ injβ x β eβ β₯ injβ y β eβ ]
