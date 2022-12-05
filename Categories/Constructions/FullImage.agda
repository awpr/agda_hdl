{-# OPTIONS --safe #-}

-- A very simple idea with (as with everything in category theory) an
-- initially-impenetrable name: the full image of `F : Functor 𝓒 𝓓` is
-- the category whose objects are the objects of `𝓒`, and whose
-- morphisms from `A` to `B` are `F ₀ A 𝓓.⇒ F ₀ B`.  So, for example,
-- the full image of the List functor is the category of functions
-- between lists.
--
-- Another perspective: the full image is the midpoint when
-- factorizing `F : Functor 𝓒 𝓓` into `Im₀ F ○ Im₁ F`, where
-- `Im₁ F : Functor 𝓒 (FullImage F)` uses only `F.map₀` and
-- `Im₀ F : Functor (FullImage F) 𝓓` uses only `F.map₁`.
--
-- https://ncatlab.org/nlab/show/full+image

open import Categories.Category using (Category)

module Categories.Constructions.FullImage
    {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
    {𝓒 : Category o₁ m₁ ℓ₁}
    {𝓓 : Category o₂ m₂ ℓ₂}
    where

open import Data.Product using (_,_)
open import Function using (_on_; _$_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Bifunctor using
  ( Bifunctor; first-second-comm
  ; Partialʳ; Partialˡ; Flip; flip⟹
  ; RightAssociated; LeftAssociated
  )
open import Categories.Category.Functors using
  ( Fun; conj-id; conj-∘; natIso
  ; wrapNatIso; unwrapNatIso
  )
open import Categories.Constructions.Product using (_⨂_)
open import Categories.Functor using
  ( Functor; map₁-id; map₁-∘; map₁-resp-≈
  ; Id; _○_; _⁂_; P₁; P₂; _▲_
  )
open import Categories.Functor.Monoidal using
  ( StrongMonoidalFunctor; StrongMonoidal; FlipSMF
  )
open import Categories.Monoidal using (Monoidal; MonoidalCategory; bundle; FlipMC)
open import Categories.Inverse using
  ( liftInverseOf; liftRetracts; inverse; left-inverse; right-inverse
  ; _¹; _⁻¹; f⁻¹; ≅-sym; _[_≅_]
  )
open import Categories.NaturalTransformation using (α; naturality; _⟹_; wrapNT)

open Categories.Functor.FunctorOperators

module _ where
  private
    module 𝓒 = Category 𝓒
    module 𝓓 = Category 𝓓

  FullImage : Functor 𝓒 𝓓 → Category o₁ m₂ ℓ₂
  FullImage F = record
    { Obj = 𝓒.Obj
    ; _⇒_ = 𝓓._⇒_ on F.map₀
    ; _≈_ = 𝓓._≈_
    ; id = 𝓓.id
    ; _∘_ = 𝓓._∘_
    ; equiv = 𝓓.equiv
    ; ∘-resp-≈ = 𝓓.∘-resp-≈
    ; ∘-idˡ = 𝓓.∘-idˡ
    ; ∘-idʳ = 𝓓.∘-idʳ
    ; ∘-assocˡ = 𝓓.∘-assocˡ
    }
    where module F = Functor F

  -- Use F.map₁ to get from 𝓒 to FullImage F.
  Im₁ : (F : Functor 𝓒 𝓓) → Functor 𝓒 (FullImage F)
  Im₁ F = record
    { map₀ = Function.id
    ; map₁ = F.map₁
    ; map₁-resp-≈ = F.map₁-resp-≈
    ; map₁-id = F.map₁-id
    ; map₁-∘ = F.map₁-∘
    }
    where module F = Functor F

  -- Use F.map₀ to get from FullImage F to 𝓓.
  Im₀ : (F : Functor 𝓒 𝓓) → Functor (FullImage F) 𝓓
  Im₀ F = record
    { map₀ = F.map₀
    ; map₁ = Function.id
    ; map₁-resp-≈ = Function.id
    ; map₁-id = 𝓓.≈.refl
    ; map₁-∘ = 𝓓.≈.refl
    }
    where module F = Functor F

  {-
  These are no longer definitionally equal; this will have to wait for a
  suitable equivalence relation of functors.

  Im₀∘Im₁≡F : ∀ {F} → Im₀ F ∘F Im₁ F ≡ F
  Im₀∘Im₁≡F = ≡.refl -- Easier than expected!
  -}

-- We'll need the same proofs in two directions, so parameterize them
-- over the monoidal structure and use them for both the original
-- monoidal structure and the flipped monoidal structure.
module MonoidalImpl
    {mc : Monoidal 𝓒} {md : Monoidal 𝓓}
    (F : StrongMonoidalFunctor (bundle mc) (bundle md))
    where
  module 𝓓 = MonoidalCategory (bundle md)
  module 𝓒 = MonoidalCategory (bundle mc)
  module F = StrongMonoidalFunctor F
  open 𝓓 hiding (monoidal; unitˡ⁺; unitˡ)
  open 𝓓.≈-Reasoning
  open Categories.Inverse.In 𝓓 using (transposeʳ⁻; transposeˡ⁺; transposeˡ⁻; ∘-inverseˡ)

  Im : Category _ _ _
  Im = FullImage F.F

  F₁○-⊗- : Bifunctor Im Im Im
  F₁○-⊗- = record
    { map₀ = 𝓒.-⊗- ₀_
    ; map₁ = λ f → F.zip ∘ (𝓓.-⊗- ₁ f) ∘ F.unzip
    ; map₁-resp-≈ = λ f≈g → ∘-resp-≈ʳ (∘-resp-≈ˡ (𝓓.-⊗- ₂ f≈g))
    ; map₁-id =
        begin
          F.zip ∘ (𝓓.-⊗- ₁$ id , id) ∘ F.unzip

        ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (𝓓.-⊗- .map₁-id)) ⟩
          F.zip ∘ id ∘ F.unzip

        ≈⟨ conj-id (≅-sym F.zipping) ⟩
          id
        ∎
    ; map₁-∘ = λ
        { {_} {_} {_} {f = f₁ , f₂} {g = g₁ , g₂} →
            begin
              F.zip ∘
              𝓓.-⊗- ₁ (f₁ ∘ g₁ , f₂ ∘ g₂) ∘
              F.unzip

            ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (𝓓.-⊗- .Functor.map₁-∘)) ⟩
              F.zip ∘
              (𝓓.-⊗- ₁ (f₁ , f₂) ∘ 𝓓.-⊗- ₁ (g₁ , g₂)) ∘
              F.unzip

            ≈˘⟨ conj-∘ (≅-sym F.zipping) ⟩
              (F.zip ∘ 𝓓.-⊗- ₁ (f₁ , f₂) ∘ F.unzip) ∘
              (F.zip ∘ 𝓓.-⊗- ₁ (g₁ , g₂) ∘ F.unzip)
            ∎
        }
    }

  unitalˡ⁺ : ∀ {A} → (F.zip ∘ -⊗- ₁ (F.zip₀ , id)) ∘ 𝓓.unitˡ⁺ ≈ F.map₁ (𝓒.unitˡ⁺ {A})
  unitalˡ⁺ =
    begin
      (F.zip ∘ -⊗- ₁ (F.zip₀ , id)) ∘ 𝓓.unitˡ⁺

    ≈⟨ transposeʳ⁻ (𝓓.unitˡ .inverse .left-inverse)
         (transposeˡ⁺ (liftRetracts F.F (𝓒.unitˡ .inverse .right-inverse))
           F.unitalˡ) ⟩
      F.map₁ 𝓒.unitˡ⁺
    ∎

  unitˡ⁺ : Id ⟹ Partialʳ F₁○-⊗- 𝓒.𝟏
  unitˡ⁺ = wrapNT record
    { α = F.map₁ 𝓒.unitˡ⁺
    ; naturality = λ {A} {B} {f} →
        begin
          F.map₁ 𝓒.unitˡ⁺ ∘ f

        ≈˘⟨ ∘-resp-≈ˡ unitalˡ⁺ ⟩
          ((F.zip ∘ -⊗- ₁ (F.zip₀ , id)) ∘ 𝓓.unitˡ⁺) ∘ f

        ≈⟨ ∘∘-resp-≈ʳ ((𝓓.unitˡ ¹) .naturality)  ⟩
          (F.zip ∘ -⊗- ₁ (F.zip₀ , id)) ∘ -⊗- ₁ (id , f) ∘ 𝓓.unitˡ⁺

        ≈⟨ ∘∘-resp-≈ʳ (∘∘-resp-≈ˡ (first-second-comm -⊗-)) ⟩
          F.zip ∘ (-⊗- ₁ (id , f) ∘ -⊗- ₁ (F.zip₀ , id)) ∘ 𝓓.unitˡ⁺

        ≈⟨ ∘-resp-≈ʳ (∘∘-resp-≈ʳ (≈.sym (∘-inverseˡ (F.zipping .inverse .left-inverse)))) ⟩
          F.zip ∘ -⊗- ₁ (id , f) ∘ F.unzip ∘
          F.zip ∘ -⊗- ₁ (F.zip₀ , id) ∘ 𝓓.unitˡ⁺

        ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ʳ (≈.trans ∘-assocˡ unitalˡ⁺))) ⟩
          F.zip ∘ -⊗- ₁ (id , f) ∘ F.unzip ∘
          F.map₁ 𝓒.unitˡ⁺

        ≈⟨ ≈.trans ∘-assocˡ (∘∘-resp-≈ˡ ∘-assocʳ) ⟩
          (F.zip ∘ -⊗- ₁ (id , f) ∘ F.unzip) ∘
          F.map₁ 𝓒.unitˡ⁺
        ∎
    }

  unitˡ : Fun _ _ [ Id ≅ Partialʳ F₁○-⊗- 𝓒.𝟏 ]
  unitˡ = natIso _ _ unitˡ⁺ $
    record
      { f⁻¹ = F.map₁ 𝓒.unitˡ⁻
      ; inverse = record
          { left-inverse = liftRetracts F.F (𝓒.unitˡ .inverse .right-inverse)
          ; right-inverse = liftRetracts F.F (𝓒.unitˡ .inverse .left-inverse)
          }
      }

module FullImageMonoidal
    {mc : Monoidal 𝓒} {md : Monoidal 𝓓}
    (F : StrongMonoidalFunctor (bundle mc) (bundle md))
    where
  module 𝓒 = MonoidalCategory (bundle mc)
  module 𝓓 = MonoidalCategory (bundle md)
  module F = StrongMonoidalFunctor F

  𝓕 : Category _ _ _
  𝓕 = FullImage F.F

  open Categories.Inverse.In 𝓕 using (Inverse)

  -⊗- : Bifunctor 𝓕 𝓕 𝓕
  -⊗- = MonoidalImpl.F₁○-⊗- F

  -⊗-⊗- : Functor (𝓕 ⨂ 𝓕 ⨂ 𝓕) 𝓕
  -⊗-⊗- = RightAssociated -⊗-

  [-⊗-]⊗- : Functor (𝓕 ⨂ 𝓕 ⨂ 𝓕) 𝓕
  [-⊗-]⊗- = LeftAssociated -⊗-

  -- A rearrangement of `F.associative` to unpack `F.map₁ 𝓒′.assocˡ`
  -- into a composition of we can commute things across
  module _ where
    open Category 𝓓
    open 𝓓.≈-Reasoning
    open Categories.Inverse.In 𝓓 using
      ( transposeʳ⁺; transposeˡ⁻; Retracts-∘
      ; ∘-inverseʳ
      )

    associativeˡ
      : ∀ {A B C}
      → F.map₁ 𝓒.assocˡ ≈
          F.zip {_} {C} ∘
          (𝓓.-⊗- ₁ (F.zip {A} {B} , id) ∘ 𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)) ∘
          F.unzip
    associativeˡ =
      begin
        F.map₁ 𝓒.assocˡ

      ≈⟨ transposeʳ⁺
           (Retracts-∘ (F.zipping .inverse .right-inverse)
             (Retracts-∘
               (liftRetracts 𝓓.-⊗- (∘-idʳ , F.zipping .inverse .right-inverse))
               (𝓓.assoc .inverse .left-inverse)))
           (transposeˡ⁻
             (liftRetracts F.F (𝓒.assoc .inverse .right-inverse))
             F.associative) ⟩
        (F.zip ∘ 𝓓.-⊗- ₁ (F.zip , id)) ∘
          (𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)) ∘ F.unzip

      ≈⟨ ≈.trans ∘-assocʳ (∘-resp-≈ʳ ∘-assocˡ) ⟩
        F.zip ∘
          (𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)) ∘
          F.unzip
      ∎

    assocˡ-work
      : ∀ {A₁ A₂ B₁ B₂ C₁ C₂}
          (f₁ : F.F ₀ A₁ ⇒ F.F ₀ A₂)
          (f₂ : F.F ₀ B₁ ⇒ F.F ₀ B₂)
          (f₃ : F.F ₀ C₁ ⇒ F.F ₀ C₂)
      → (𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)) ∘
          𝓓.-⊗- ₁ (f₁ , F.zip ∘ 𝓓.-⊗- ₁ (f₂ , f₃) ∘ F.unzip) ≈
        (𝓓.-⊗- ₁ (F.zip ∘ 𝓓.-⊗- ₁ (f₁ , f₂) ∘ F.unzip , f₃) ∘
          𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip))
    assocˡ-work f₁ f₂ f₃ =
      begin
        (𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)) ∘
          𝓓.-⊗- ₁ (f₁ , F.zip ∘ 𝓓.-⊗- ₁ (f₂ , f₃) ∘ F.unzip)

      ≈⟨ ∘∘-resp-≈ʳ (∘∘-resp-≈ʳ (≈.sym (Functor.map₁-∘ 𝓓.-⊗-)))  ⟩
        𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘
          𝓓.-⊗- ₁ (id ∘ f₁ , F.unzip ∘ F.zip ∘ 𝓓.-⊗- ₁ (f₂ , f₃) ∘ F.unzip)

      ≈⟨ ∘-resp-≈ʳ
           (∘-resp-≈ʳ
             (𝓓.-⊗- ₂
               ( ≈.trans ∘-idˡ (≈.sym ∘-idʳ)
               , ≈.trans (∘∘-resp-≈ˡ (F.zipping .inverse .left-inverse)) ∘-idˡ)
               ))
       ⟩
        𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘
          𝓓.-⊗- ₁ (f₁ ∘ id , 𝓓.-⊗- ₁ (f₂ , f₃) ∘ F.unzip)

      ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (Functor.map₁-∘ 𝓓.-⊗-)) ⟩
        𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘
          𝓓.-⊗- ₁ (f₁ , 𝓓.-⊗- ₁ (f₂ , f₃)) ∘
          𝓓.-⊗- ₁ (id , F.unzip)

      ≈⟨ ∘-resp-≈ʳ (≈.trans (∘∘-resp-≈ˡ (𝓓.assoc ._¹ .naturality)) ∘-assocʳ) ⟩
        𝓓.-⊗- ₁ (F.zip , id) ∘
          𝓓.-⊗- ₁ (𝓓.-⊗- ₁ (f₁ , f₂) , f₃) ∘
          𝓓.assocˡ ∘
          𝓓.-⊗- ₁ (id , F.unzip)

      ≈⟨ ∘∘-resp-≈ˡ (≈.sym (Functor.map₁-∘ 𝓓.-⊗-)) ⟩
        𝓓.-⊗- ₁ (F.zip ∘ 𝓓.-⊗- ₁ (f₁ , f₂) , id ∘ f₃) ∘
          𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)

      ≈⟨ ∘-resp-≈ˡ
           (𝓓.-⊗- ₂
             ( ∘-resp-≈ʳ (≈.trans (≈.sym (∘-inverseʳ F.unzip∘zip)) ∘-assocʳ)
             , ≈.trans ∘-idˡ (≈.sym ∘-idʳ)
             ))
       ⟩
        𝓓.-⊗- ₁ (F.zip ∘ 𝓓.-⊗- ₁ (f₁ , f₂) ∘ F.unzip ∘ F.zip , f₃ ∘ id) ∘
          𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)

      ≈⟨ ∘-resp-≈ˡ (𝓓.-⊗- ₂ (≈.trans (∘-resp-≈ʳ ∘-assocˡ) ∘-assocˡ , ≈.refl)) ⟩
        𝓓.-⊗- ₁ ((F.zip ∘ 𝓓.-⊗- ₁ (f₁ , f₂) ∘ F.unzip) ∘ F.zip , f₃ ∘ id) ∘
          𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)

      ≈˘⟨ ∘∘-resp-≈ˡ (≈.sym (Functor.map₁-∘ 𝓓.-⊗-)) ⟩
        𝓓.-⊗- ₁ (F.zip ∘ 𝓓.-⊗- ₁ (f₁ , f₂) ∘ F.unzip , f₃) ∘
          𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)
      ∎

    assocˡ : RightAssociated -⊗- ⟹ LeftAssociated -⊗-
    assocˡ = wrapNT record
      { α = F.map₁ 𝓒.assocˡ
      ; naturality = λ
          { {A₁ , A₂ , A₃} {B₁ , B₂ , B₃} {f₁ , f₂ , f₃} →
              begin
                F.map₁ 𝓒.assocˡ ∘ RightAssociated -⊗- ₁ (f₁ , f₂ , f₃)

              ≈⟨ ∘-resp-≈ˡ associativeˡ ⟩
                (F.zip ∘
                  (𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)) ∘
                  F.unzip) ∘
                (F.zip ∘ 𝓓.-⊗- ₁ (f₁ , F.zip ∘ 𝓓.-⊗- ₁ (f₂ , f₃) ∘ F.unzip) ∘ F.unzip)

              ≈⟨ conj-∘ (≅-sym F.zipping) ⟩
                F.zip ∘
                ((𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)) ∘
                  𝓓.-⊗- ₁ (f₁ , F.zip ∘ 𝓓.-⊗- ₁ (f₂ , f₃) ∘ F.unzip)) ∘
                F.unzip

              ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (assocˡ-work f₁ f₂ f₃)) ⟩
                F.zip ∘
                (𝓓.-⊗- ₁ (F.zip ∘ 𝓓.-⊗- ₁ (f₁ , f₂) ∘ F.unzip , f₃) ∘
                  𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)) ∘
                F.unzip

              ≈˘⟨ conj-∘ (≅-sym F.zipping) ⟩
                (F.zip ∘ 𝓓.-⊗- ₁ (F.zip ∘ 𝓓.-⊗- ₁ (f₁ , f₂) ∘ F.unzip , f₃) ∘ F.unzip) ∘
                F.zip ∘ (𝓓.-⊗- ₁ (F.zip , id) ∘ 𝓓.assocˡ ∘ 𝓓.-⊗- ₁ (id , F.unzip)) ∘ F.unzip

              ≈˘⟨ ∘-resp-≈ʳ associativeˡ ⟩
                LeftAssociated -⊗- ₁ (f₁ , f₂ , f₃) ∘ F.map₁ 𝓒.assocˡ
              ∎
          }
      }

  assocˡ⁻¹ : ∀ {A} → Inverse (assocˡ .α {A})
  assocˡ⁻¹ = record
    { f⁻¹ = F.map₁ 𝓒.assocʳ
    ; inverse = record
        { left-inverse = liftRetracts F.F (𝓒.assoc .inverse .right-inverse)
        ; right-inverse = liftRetracts F.F (𝓒.assoc .inverse .left-inverse)
        }
    }

  assoc : Fun (𝓕 ⨂ 𝓕 ⨂ 𝓕) 𝓕 [ _ ≅ _ ]
  assoc = natIso (𝓕 ⨂ 𝓕 ⨂ 𝓕) 𝓕 assocˡ assocˡ⁻¹

  unitˡ : Fun 𝓕 𝓕 [ Id ≅ _ ]
  unitˡ = MonoidalImpl.unitˡ F

  unitʳ : Fun 𝓕 𝓕 [ Id ≅ _ ]
  unitʳ = MonoidalImpl.unitˡ (FlipSMF F)

  monoidal : Monoidal 𝓕
  monoidal = record
    { 𝟏 =  𝓒.𝟏
    ; -⊗- = -⊗-
    ; assoc = wrapNatIso (unwrapNatIso assoc)
    ; unitˡ = wrapNatIso (unwrapNatIso unitˡ)
    ; unitʳ = wrapNatIso (unwrapNatIso unitʳ)
    }

open FullImageMonoidal public using (monoidal)
