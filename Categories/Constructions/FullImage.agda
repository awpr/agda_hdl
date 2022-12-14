{-# OPTIONS --safe #-}

-- A very simple idea with (as with everything in category theory) an
-- initially-impenetrable name: the full image of `F : Functor ð ð` is
-- the category whose objects are the objects of `ð`, and whose
-- morphisms from `A` to `B` are `F â A ð.â F â B`.  So, for example,
-- the full image of the List functor is the category of functions
-- between lists.
--
-- Another perspective: the full image is the midpoint when
-- factorizing `F : Functor ð ð` into `Imâ F â Imâ F`, where
-- `Imâ F : Functor ð (FullImage F)` uses only `F.mapâ` and
-- `Imâ F : Functor (FullImage F) ð` uses only `F.mapâ`.
--
-- https://ncatlab.org/nlab/show/full+image

open import Categories.Category using (Category)

module Categories.Constructions.FullImage
    {oâ mâ ââ oâ mâ ââ}
    {ð : Category oâ mâ ââ}
    {ð : Category oâ mâ ââ}
    where

open import Data.Product using (_,_)
open import Function using (_on_; _$_)
open import Relation.Binary.PropositionalEquality as â¡ using (_â¡_)

open import Categories.Bifunctor using
  ( Bifunctor; first-second-comm
  ; PartialÊ³; PartialË¡; Flip; flipâ¹
  ; RightAssociated; LeftAssociated
  )
open import Categories.Category.Functors using
  ( Fun; conj-id; conj-â; natIso
  ; wrapNatIso; unwrapNatIso
  )
open import Categories.Constructions.Product using (_â¨_)
open import Categories.Functor using
  ( Functor; mapâ-id; mapâ-â; mapâ-resp-â
  ; Id; _â_; _â_; Pâ; Pâ; _â²_
  )
open import Categories.Functor.Monoidal using
  ( StrongMonoidalFunctor; StrongMonoidal; FlipSMF
  )
open import Categories.Monoidal using (Monoidal; MonoidalCategory; bundle; FlipMC)
open import Categories.Inverse using
  ( liftInverseOf; liftRetracts; inverse; left-inverse; right-inverse
  ; _Â¹; _â»Â¹; fâ»Â¹; â-sym; _[_â_]
  )
open import Categories.NaturalTransformation using (Î±; naturality; _â¹_; wrapNT)

open Categories.Functor.FunctorOperators

module _ where
  private
    module ð = Category ð
    module ð = Category ð

  FullImage : Functor ð ð â Category oâ mâ ââ
  FullImage F = record
    { Obj = ð.Obj
    ; _â_ = ð._â_ on F.mapâ
    ; _â_ = ð._â_
    ; id = ð.id
    ; _â_ = ð._â_
    ; equiv = ð.equiv
    ; â-resp-â = ð.â-resp-â
    ; â-idË¡ = ð.â-idË¡
    ; â-idÊ³ = ð.â-idÊ³
    ; â-assocË¡ = ð.â-assocË¡
    }
    where module F = Functor F

  -- Use F.mapâ to get from ð to FullImage F.
  Imâ : (F : Functor ð ð) â Functor ð (FullImage F)
  Imâ F = record
    { mapâ = Function.id
    ; mapâ = F.mapâ
    ; mapâ-resp-â = F.mapâ-resp-â
    ; mapâ-id = F.mapâ-id
    ; mapâ-â = F.mapâ-â
    }
    where module F = Functor F

  -- Use F.mapâ to get from FullImage F to ð.
  Imâ : (F : Functor ð ð) â Functor (FullImage F) ð
  Imâ F = record
    { mapâ = F.mapâ
    ; mapâ = Function.id
    ; mapâ-resp-â = Function.id
    ; mapâ-id = ð.â.refl
    ; mapâ-â = ð.â.refl
    }
    where module F = Functor F

  {-
  These are no longer definitionally equal; this will have to wait for a
  suitable equivalence relation of functors.

  ImââImââ¡F : â {F} â Imâ F âF Imâ F â¡ F
  ImââImââ¡F = â¡.refl -- Easier than expected!
  -}

-- We'll need the same proofs in two directions, so parameterize them
-- over the monoidal structure and use them for both the original
-- monoidal structure and the flipped monoidal structure.
module MonoidalImpl
    {mc : Monoidal ð} {md : Monoidal ð}
    (F : StrongMonoidalFunctor (bundle mc) (bundle md))
    where
  module ð = MonoidalCategory (bundle md)
  module ð = MonoidalCategory (bundle mc)
  module F = StrongMonoidalFunctor F
  open ð hiding (monoidal; unitË¡âº; unitË¡)
  open ð.â-Reasoning
  open Categories.Inverse.In ð using (transposeÊ³â»; transposeË¡âº; transposeË¡â»; â-inverseË¡)

  Im : Category _ _ _
  Im = FullImage F.F

  Fââ-â- : Bifunctor Im Im Im
  Fââ-â- = record
    { mapâ = ð.-â- â_
    ; mapâ = Î» f â F.zip â (ð.-â- â f) â F.unzip
    ; mapâ-resp-â = Î» fâg â â-resp-âÊ³ (â-resp-âË¡ (ð.-â- â fâg))
    ; mapâ-id =
        begin
          F.zip â (ð.-â- â$ id , id) â F.unzip

        ââ¨ â-resp-âÊ³ (â-resp-âË¡ (ð.-â- .mapâ-id)) â©
          F.zip â id â F.unzip

        ââ¨ conj-id (â-sym F.zipping) â©
          id
        â
    ; mapâ-â = Î»
        { {_} {_} {_} {f = fâ , fâ} {g = gâ , gâ} â
            begin
              F.zip â
              ð.-â- â (fâ â gâ , fâ â gâ) â
              F.unzip

            ââ¨ â-resp-âÊ³ (â-resp-âË¡ (ð.-â- .Functor.mapâ-â)) â©
              F.zip â
              (ð.-â- â (fâ , fâ) â ð.-â- â (gâ , gâ)) â
              F.unzip

            âËâ¨ conj-â (â-sym F.zipping) â©
              (F.zip â ð.-â- â (fâ , fâ) â F.unzip) â
              (F.zip â ð.-â- â (gâ , gâ) â F.unzip)
            â
        }
    }

  unitalË¡âº : â {A} â (F.zip â -â- â (F.zipâ , id)) â ð.unitË¡âº â F.mapâ (ð.unitË¡âº {A})
  unitalË¡âº =
    begin
      (F.zip â -â- â (F.zipâ , id)) â ð.unitË¡âº

    ââ¨ transposeÊ³â» (ð.unitË¡ .inverse .left-inverse)
         (transposeË¡âº (liftRetracts F.F (ð.unitË¡ .inverse .right-inverse))
           F.unitalË¡) â©
      F.mapâ ð.unitË¡âº
    â

  unitË¡âº : Id â¹ PartialÊ³ Fââ-â- ð.ð
  unitË¡âº = wrapNT record
    { Î± = F.mapâ ð.unitË¡âº
    ; naturality = Î» {A} {B} {f} â
        begin
          F.mapâ ð.unitË¡âº â f

        âËâ¨ â-resp-âË¡ unitalË¡âº â©
          ((F.zip â -â- â (F.zipâ , id)) â ð.unitË¡âº) â f

        ââ¨ ââ-resp-âÊ³ ((ð.unitË¡ Â¹) .naturality)  â©
          (F.zip â -â- â (F.zipâ , id)) â -â- â (id , f) â ð.unitË¡âº

        ââ¨ ââ-resp-âÊ³ (ââ-resp-âË¡ (first-second-comm -â-)) â©
          F.zip â (-â- â (id , f) â -â- â (F.zipâ , id)) â ð.unitË¡âº

        ââ¨ â-resp-âÊ³ (ââ-resp-âÊ³ (â.sym (â-inverseË¡ (F.zipping .inverse .left-inverse)))) â©
          F.zip â -â- â (id , f) â F.unzip â
          F.zip â -â- â (F.zipâ , id) â ð.unitË¡âº

        ââ¨ â-resp-âÊ³ (â-resp-âÊ³ (â-resp-âÊ³ (â.trans â-assocË¡ unitalË¡âº))) â©
          F.zip â -â- â (id , f) â F.unzip â
          F.mapâ ð.unitË¡âº

        ââ¨ â.trans â-assocË¡ (ââ-resp-âË¡ â-assocÊ³) â©
          (F.zip â -â- â (id , f) â F.unzip) â
          F.mapâ ð.unitË¡âº
        â
    }

  unitË¡ : Fun _ _ [ Id â PartialÊ³ Fââ-â- ð.ð ]
  unitË¡ = natIso _ _ unitË¡âº $
    record
      { fâ»Â¹ = F.mapâ ð.unitË¡â»
      ; inverse = record
          { left-inverse = liftRetracts F.F (ð.unitË¡ .inverse .right-inverse)
          ; right-inverse = liftRetracts F.F (ð.unitË¡ .inverse .left-inverse)
          }
      }

module FullImageMonoidal
    {mc : Monoidal ð} {md : Monoidal ð}
    (F : StrongMonoidalFunctor (bundle mc) (bundle md))
    where
  module ð = MonoidalCategory (bundle mc)
  module ð = MonoidalCategory (bundle md)
  module F = StrongMonoidalFunctor F

  ð : Category _ _ _
  ð = FullImage F.F

  open Categories.Inverse.In ð using (Inverse)

  -â- : Bifunctor ð ð ð
  -â- = MonoidalImpl.Fââ-â- F

  -â-â- : Functor (ð â¨ ð â¨ ð) ð
  -â-â- = RightAssociated -â-

  [-â-]â- : Functor (ð â¨ ð â¨ ð) ð
  [-â-]â- = LeftAssociated -â-

  -- A rearrangement of `F.associative` to unpack `F.mapâ ðâ².assocË¡`
  -- into a composition of we can commute things across
  module _ where
    open Category ð
    open ð.â-Reasoning
    open Categories.Inverse.In ð using
      ( transposeÊ³âº; transposeË¡â»; Retracts-â
      ; â-inverseÊ³
      )

    associativeË¡
      : â {A B C}
      â F.mapâ ð.assocË¡ â
          F.zip {_} {C} â
          (ð.-â- â (F.zip {A} {B} , id) â ð.assocË¡ â ð.-â- â (id , F.unzip)) â
          F.unzip
    associativeË¡ =
      begin
        F.mapâ ð.assocË¡

      ââ¨ transposeÊ³âº
           (Retracts-â (F.zipping .inverse .right-inverse)
             (Retracts-â
               (liftRetracts ð.-â- (â-idÊ³ , F.zipping .inverse .right-inverse))
               (ð.assoc .inverse .left-inverse)))
           (transposeË¡â»
             (liftRetracts F.F (ð.assoc .inverse .right-inverse))
             F.associative) â©
        (F.zip â ð.-â- â (F.zip , id)) â
          (ð.assocË¡ â ð.-â- â (id , F.unzip)) â F.unzip

      ââ¨ â.trans â-assocÊ³ (â-resp-âÊ³ â-assocË¡) â©
        F.zip â
          (ð.-â- â (F.zip , id) â ð.assocË¡ â ð.-â- â (id , F.unzip)) â
          F.unzip
      â

    assocË¡-work
      : â {Aâ Aâ Bâ Bâ Câ Câ}
          (fâ : F.F â Aâ â F.F â Aâ)
          (fâ : F.F â Bâ â F.F â Bâ)
          (fâ : F.F â Câ â F.F â Câ)
      â (ð.-â- â (F.zip , id) â ð.assocË¡ â ð.-â- â (id , F.unzip)) â
          ð.-â- â (fâ , F.zip â ð.-â- â (fâ , fâ) â F.unzip) â
        (ð.-â- â (F.zip â ð.-â- â (fâ , fâ) â F.unzip , fâ) â
          ð.-â- â (F.zip , id) â ð.assocË¡ â ð.-â- â (id , F.unzip))
    assocË¡-work fâ fâ fâ =
      begin
        (ð.-â- â (F.zip , id) â ð.assocË¡ â ð.-â- â (id , F.unzip)) â
          ð.-â- â (fâ , F.zip â ð.-â- â (fâ , fâ) â F.unzip)

      ââ¨ ââ-resp-âÊ³ (ââ-resp-âÊ³ (â.sym (Functor.mapâ-â ð.-â-)))  â©
        ð.-â- â (F.zip , id) â ð.assocË¡ â
          ð.-â- â (id â fâ , F.unzip â F.zip â ð.-â- â (fâ , fâ) â F.unzip)

      ââ¨ â-resp-âÊ³
           (â-resp-âÊ³
             (ð.-â- â
               ( â.trans â-idË¡ (â.sym â-idÊ³)
               , â.trans (ââ-resp-âË¡ (F.zipping .inverse .left-inverse)) â-idË¡)
               ))
       â©
        ð.-â- â (F.zip , id) â ð.assocË¡ â
          ð.-â- â (fâ â id , ð.-â- â (fâ , fâ) â F.unzip)

      ââ¨ â-resp-âÊ³ (â-resp-âÊ³ (Functor.mapâ-â ð.-â-)) â©
        ð.-â- â (F.zip , id) â ð.assocË¡ â
          ð.-â- â (fâ , ð.-â- â (fâ , fâ)) â
          ð.-â- â (id , F.unzip)

      ââ¨ â-resp-âÊ³ (â.trans (ââ-resp-âË¡ (ð.assoc ._Â¹ .naturality)) â-assocÊ³) â©
        ð.-â- â (F.zip , id) â
          ð.-â- â (ð.-â- â (fâ , fâ) , fâ) â
          ð.assocË¡ â
          ð.-â- â (id , F.unzip)

      ââ¨ ââ-resp-âË¡ (â.sym (Functor.mapâ-â ð.-â-)) â©
        ð.-â- â (F.zip â ð.-â- â (fâ , fâ) , id â fâ) â
          ð.assocË¡ â ð.-â- â (id , F.unzip)

      ââ¨ â-resp-âË¡
           (ð.-â- â
             ( â-resp-âÊ³ (â.trans (â.sym (â-inverseÊ³ F.unzipâzip)) â-assocÊ³)
             , â.trans â-idË¡ (â.sym â-idÊ³)
             ))
       â©
        ð.-â- â (F.zip â ð.-â- â (fâ , fâ) â F.unzip â F.zip , fâ â id) â
          ð.assocË¡ â ð.-â- â (id , F.unzip)

      ââ¨ â-resp-âË¡ (ð.-â- â (â.trans (â-resp-âÊ³ â-assocË¡) â-assocË¡ , â.refl)) â©
        ð.-â- â ((F.zip â ð.-â- â (fâ , fâ) â F.unzip) â F.zip , fâ â id) â
          ð.assocË¡ â ð.-â- â (id , F.unzip)

      âËâ¨ ââ-resp-âË¡ (â.sym (Functor.mapâ-â ð.-â-)) â©
        ð.-â- â (F.zip â ð.-â- â (fâ , fâ) â F.unzip , fâ) â
          ð.-â- â (F.zip , id) â ð.assocË¡ â ð.-â- â (id , F.unzip)
      â

    assocË¡ : RightAssociated -â- â¹ LeftAssociated -â-
    assocË¡ = wrapNT record
      { Î± = F.mapâ ð.assocË¡
      ; naturality = Î»
          { {Aâ , Aâ , Aâ} {Bâ , Bâ , Bâ} {fâ , fâ , fâ} â
              begin
                F.mapâ ð.assocË¡ â RightAssociated -â- â (fâ , fâ , fâ)

              ââ¨ â-resp-âË¡ associativeË¡ â©
                (F.zip â
                  (ð.-â- â (F.zip , id) â ð.assocË¡ â ð.-â- â (id , F.unzip)) â
                  F.unzip) â
                (F.zip â ð.-â- â (fâ , F.zip â ð.-â- â (fâ , fâ) â F.unzip) â F.unzip)

              ââ¨ conj-â (â-sym F.zipping) â©
                F.zip â
                ((ð.-â- â (F.zip , id) â ð.assocË¡ â ð.-â- â (id , F.unzip)) â
                  ð.-â- â (fâ , F.zip â ð.-â- â (fâ , fâ) â F.unzip)) â
                F.unzip

              ââ¨ â-resp-âÊ³ (â-resp-âË¡ (assocË¡-work fâ fâ fâ)) â©
                F.zip â
                (ð.-â- â (F.zip â ð.-â- â (fâ , fâ) â F.unzip , fâ) â
                  ð.-â- â (F.zip , id) â ð.assocË¡ â ð.-â- â (id , F.unzip)) â
                F.unzip

              âËâ¨ conj-â (â-sym F.zipping) â©
                (F.zip â ð.-â- â (F.zip â ð.-â- â (fâ , fâ) â F.unzip , fâ) â F.unzip) â
                F.zip â (ð.-â- â (F.zip , id) â ð.assocË¡ â ð.-â- â (id , F.unzip)) â F.unzip

              âËâ¨ â-resp-âÊ³ associativeË¡ â©
                LeftAssociated -â- â (fâ , fâ , fâ) â F.mapâ ð.assocË¡
              â
          }
      }

  assocË¡â»Â¹ : â {A} â Inverse (assocË¡ .Î± {A})
  assocË¡â»Â¹ = record
    { fâ»Â¹ = F.mapâ ð.assocÊ³
    ; inverse = record
        { left-inverse = liftRetracts F.F (ð.assoc .inverse .right-inverse)
        ; right-inverse = liftRetracts F.F (ð.assoc .inverse .left-inverse)
        }
    }

  assoc : Fun (ð â¨ ð â¨ ð) ð [ _ â _ ]
  assoc = natIso (ð â¨ ð â¨ ð) ð assocË¡ assocË¡â»Â¹

  unitË¡ : Fun ð ð [ Id â _ ]
  unitË¡ = MonoidalImpl.unitË¡ F

  unitÊ³ : Fun ð ð [ Id â _ ]
  unitÊ³ = MonoidalImpl.unitË¡ (FlipSMF F)

  monoidal : Monoidal ð
  monoidal = record
    { ð =  ð.ð
    ; -â- = -â-
    ; assoc = wrapNatIso (unwrapNatIso assoc)
    ; unitË¡ = wrapNatIso (unwrapNatIso unitË¡)
    ; unitÊ³ = wrapNatIso (unwrapNatIso unitÊ³)
    }

open FullImageMonoidal public using (monoidal)
