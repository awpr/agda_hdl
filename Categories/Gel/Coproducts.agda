open import Categories.Cartesian using (CartesianCategory)
open import Categories.Coproducts using (Coproducts)

module Categories.Gel.Coproducts
    {o m β}
    (π : CartesianCategory o m β)
    (coproducts : Coproducts (CartesianCategory.π€ π))
    where

open CartesianCategory π hiding (_β_)
open Coproducts coproducts

open import Categories.Gel.Cartesian π

injβ : β {A B} β β¦ A β§ βΆ β¦ A β B β§
injβ f = iβ β f

injβ : β {A B} β β¦ B β§ βΆ β¦ A β B β§
injβ f = iβ β f

-- Given only a bicartesian (not distributive) category, we can't
-- distribute the "context" inside a coproduct, so when matching
-- coproducts, we can't provide access to that context inside each arm
-- of the match.  As such, the morphism arguments here are _ββ_ rather
-- than _β¨ X β©β_.
β-elim _β₯_ : β {A B C} β (β¦ A β§ ββ β¦ C β§) β (β¦ B β§ ββ β¦ C β§) β β¦ A β B β§ βΆ β¦ C β§
(f β₯ g) x = (reifyβ² f β½ reifyβ² g) β x

β-elim = _β₯_

syntax β-elim (Ξ» x β eβ) (Ξ» y β eβ) eβ = case eβ of [ x β eβ β₯ y β eβ ]
