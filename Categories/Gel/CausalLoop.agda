open import Categories.Cartesian using (CartesianCategory)
open import Categories.CausalLoop using (Causal)

module Categories.Gel.CausalLoop
  {o m ā}
  (š : CartesianCategory o m ā)
  (Loop : Causal (CartesianCategory.monoidalCategory š))
  where

open CartesianCategory š hiding (_Ć_)
open import Categories.Gel.Cartesian š
open import Categories.Gel.Product š

unfold
  : ā {a s} {A : Obj ā Set a} {S : Obj ā Set s}
      ā¦ _ : Yoneda A ā¦ ā¦ _ : Yoneda S ā¦
  ā S ā
  ā (S ā S Ć A) ā¶ A
unfold sā f = wrap (Causal.loop Loop (unwrap sā) (unwrap (_ā£_.unwrap (reify f))))
