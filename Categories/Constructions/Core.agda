{-# OPTIONS --safe #-}

open import Categories.Category using (Category; _[_â_])

module Categories.Constructions.Core {o m â} (ð : Category o m â) where

open import Level using (_â_)
open import Relation.Binary.Structures using (IsEquivalence)

import Categories.Inverse

open Category ð hiding (_â_)
open Categories.Inverse.In ð

record _â_ {A B : Obj} (f g : A â B) : Set â where
  field
    _Â¹ : ð [ f Â¹ â g Â¹ ]
    _â»Â¹ : ð [ f â»Â¹ â g â»Â¹ ]

open _â_ public

â-refl : â {A B} {f : A â B} â f â f
â-refl = record { _Â¹ = â.refl ; _â»Â¹ = â.refl }

â-sym : â {A B} {f g : A â B} â f â g â g â f
â-sym fâg = record { _Â¹ = â.sym (fâg Â¹) ; _â»Â¹ = â.sym (fâg â»Â¹) }

â-trans : â {A B} {f g h : A â B} â f â g â g â h â f â h
â-trans fâg gâh = record
  { _Â¹ = â.trans (fâg Â¹) (gâh Â¹)
  ; _â»Â¹ = â.trans (fâg â»Â¹) (gâh â»Â¹)
  }

â-equiv : â {A B} â IsEquivalence (_â_ {A} {B})
â-equiv = record { refl = â-refl ; sym = â-sym ; trans = â-trans }

Core : Category o (m â â) â
Core = record
  { Obj = Obj
  ; _â_ = _â_
  ; _â_ = _â_
  ; id = â-refl
  ; _â_ = Î» f g â â-trans g f
  ; equiv = â-equiv
  ; â-resp-â = Î» fââfâ gââgâ â record
      { _Â¹ = â-resp-â (fââfâ Â¹) (gââgâ Â¹)
      ; _â»Â¹ = â-resp-â (gââgâ â»Â¹) (fââfâ â»Â¹)
      }
  ; â-idË¡ = record { _Â¹ = â-idË¡ ; _â»Â¹ = â-idÊ³ }
  ; â-idÊ³ = record { _Â¹ = â-idÊ³ ; _â»Â¹ = â-idË¡ }
  ; â-assocË¡ = record { _Â¹ = â-assocË¡ ; _â»Â¹ = â-assocÊ³ }
  }
