open import Categories.Cartesian using (CartesianCategory)

module Categories.Gel.Product {o m ℓ} (𝓒 : CartesianCategory o m ℓ) where

open import Level using (Level)

open import Categories.Bifunctor renaming (first to first′; second to second′)
open import Categories.Gel.Cartesian 𝓒
open CartesianCategory 𝓒 renaming (_×_ to infixr 40 _⊗_)

private
  variable
    a b c : Level
    A : Obj → Set a
    B : Obj → Set b
    C : Obj → Set c

infixr 40 _×_
record _×_
    (A : Obj → Set a) ⦃ _ : Yoneda A ⦄
    (B : Obj → Set b) ⦃ _ : Yoneda B ⦄
    (X : Obj)
    : Set m
    where
  field
    unwrap : ⟦ Rep A ⊗ Rep B ⟧ X

instance
  yoneda× : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ → Yoneda (A × B)
  yoneda× = record { wrap = λ x → record { unwrap = x } ; unwrap = _×_.unwrap }

  module _ ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ where
    open Yoneda (yoneda× {A = A} {B = B}) public using () renaming (presheaf to presheaf×)

fst : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ → A × B ⟶ A
fst xy = wrap (proj₁ (unwrap xy))

snd : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ → A × B ⟶ B
snd xy = wrap (proj₂ (unwrap xy))

first : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ ⦃ _ : Yoneda C ⦄ → (A ⇉ C) ⟶ A × B ⇨ C × B
first f xy = wrap
  (first′ -×- (unwrap (_↣_.unwrap (reify f)) ∘ braid) ∘
   assocˡ ∘
   (id △ unwrap xy))

second : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ ⦃ _ : Yoneda C ⦄ → (B ⇉ C) ⟶ A × B ⇨ A × C
second f xy = wrap
  (second′ -×- (unwrap (_↣_.unwrap (reify f))) ∘
   assocʳ ∘
   (unwrap xy △ id))

infixr 20 _,_
_,_ : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ → A ⟶ B ⇨ A × B
x , y = wrap (unwrap x △ unwrap y)
