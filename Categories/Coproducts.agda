{-# OPTIONS --safe #-}

module Categories.Coproducts where

open import Level using (_â_)

open import Categories.Category using (Category)

record Coproducts {o m â} (ð : Category o m â) : Set (o â m â â) where
  open Category ð

  -- less than infixr 40 _Ã_ _â_; greater than infixr 30 _â_
  infixr 35 _â_ -- â is \coprod

  -- less than infixr 20 _â³_
  infixr 15 _â½_

  field
    _â_ : (A B : Obj) â Obj
    â¥ : Obj

    â! : â {A} â â¥ â A
    iâ : â {A B} â A â A â B
    iâ : â {A B} â B â A â B
    _â½_ : â {A B C} â A â C â B â C â A â B â C

    â½-resp-â
      : â {A B C} {fâ fâ : A â C} {gâ gâ : B â C}
      â fâ â fâ â gâ â gâ â fâ â½ gâ â fâ â½ gâ

  swapâ : â {A B} â A â B â B â A
  swapâ = iâ â½ iâ

  bimapâ : â {A B C D} â A â B â C â D â A â C â B â D
  bimapâ f g = iâ â f â½ iâ â g
