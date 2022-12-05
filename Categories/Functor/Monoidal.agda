{-# OPTIONS --safe #-}

open import Categories.Monoidal using (MonoidalCategory; FlipMC)

module Categories.Functor.Monoidal where

open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Level using (_⊔_)
open import Relation.Binary using (Rel)

open import Categories.Category using (Category)
open import Categories.Category.Functors using (Fun; natIso)
open import Categories.Constructions.Product using (_⨂_)
open import Categories.Functor using (Functor; _○_; _▲_; P₁; P₂)
open Categories.Functor.FunctorOperators
open import Categories.Inverse using
  ( _[_≅_]; liftRetracts
  ; inverse; left-inverse; right-inverse
  )
open import Categories.NaturalTransformation using (_⟹_; α; naturality; wrapNT)

module _
    {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
    (𝓒 : MonoidalCategory o₁ m₁ ℓ₁)
    (𝓓 : MonoidalCategory o₂ m₂ ℓ₂)
    where
  private
    module 𝓒 = MonoidalCategory 𝓒
    module 𝓓 where
      open MonoidalCategory 𝓓 public
      open Categories.Inverse.In 𝓤 public

  record LaxMonoidal (F : Functor 𝓒.𝓤 𝓓.𝓤) : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ ℓ₂) where
    open 𝓓

    -- The derived functor `λ (A , B) → F A ⊗ F B`
    F-⊗F- : Functor (𝓒.𝓤 ⨂ 𝓒.𝓤) 𝓓.𝓤
    F-⊗F- = -⊗- ○ (F ○ P₁ ▲ F ○ P₂)

    field
      zip₀ : 𝟏 ⇒ F ₀ 𝓒.𝟏

      -- A natural transformation `∀ {A B} → F A ⊗ F B ⇒ F (A ⊗ B)`
      μ : F-⊗F- ⟹ F ○ 𝓒.-⊗-

    zip : ∀ {A B} → F-⊗F- ₀ (A , B) ⇒ F ₀ (A 𝓒.⊗ B)
    zip = μ .α

    field
      associative
        : ∀ {A B C}
        → zip ∘ bimap⊗ id (zip {B} {C}) ∘ assocʳ ≈
            F ₁ 𝓒.assocʳ ∘ zip ∘ bimap⊗ (zip {A} {B}) id

      unitalˡ
        : ∀ {A}
        → F ₁ 𝓒.unitˡ⁻ ∘ zip {_} {A} ∘ bimap⊗ zip₀ id ≈ unitˡ⁻

      unitalʳ
        : ∀ {A}
        → F ₁ 𝓒.unitʳ⁻ ∘ zip {A} {_} ∘ bimap⊗ id zip₀ ≈ unitʳ⁻

  record StrongMonoidal (F : Functor 𝓒.𝓤 𝓓.𝓤) : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ ℓ₂) where
    open MonoidalCategory 𝓓

    field
      laxMonoidal : LaxMonoidal F

    open LaxMonoidal laxMonoidal public

    field
      inv-zip₀ : 𝓓.Inverse zip₀
      inv-zip : ∀ {A B} → 𝓓.Inverse (zip {A} {B})

    unzip₀ : F ₀ 𝓒.𝟏 ⇒ 𝟏
    unzip₀ = 𝓓.Inverse.f⁻¹ inv-zip₀

    unzip : ∀ {A B} → F ₀ (A 𝓒.⊗ B) ⇒ F ₀ A ⊗ F ₀ B
    unzip = 𝓓.Inverse.f⁻¹ inv-zip

    zipping : Fun _ _ [ F-⊗F- ≅ F ○ 𝓒.-⊗- ]
    zipping = natIso _ _ μ inv-zip

    μ⁻¹ : F ○ 𝓒.-⊗- ⟹ F-⊗F-
    μ⁻¹ = zipping ._[_≅_]._⁻¹

    zip∘unzip : ∀ {A B} → zip ∘ unzip ≈ id {F ₀ (A 𝓒.⊗ B)}
    zip∘unzip = 𝓓.left-inverse (𝓓.Inverse.inverse inv-zip)

    unzip∘zip : ∀ {A B} → unzip ∘ zip ≈ id {F ₀ A ⊗ F ₀ B}
    unzip∘zip = 𝓓.right-inverse (𝓓.Inverse.inverse inv-zip)

  record LaxMonoidalFunctor : Set (o₁ ⊔ m₁ ⊔ ℓ₁ ⊔ o₂ ⊔ m₂ ⊔ ℓ₂) where
    constructor bundle
    field
      {F} : Functor 𝓒.𝓤 𝓓.𝓤
      laxMonoidal : LaxMonoidal F

    open Functor F public
    open LaxMonoidal laxMonoidal public

  record StrongMonoidalFunctor : Set (o₁ ⊔ m₁ ⊔ ℓ₁ ⊔ o₂ ⊔ m₂ ⊔ ℓ₂) where
    constructor bundle
    field
      {F} : Functor 𝓒.𝓤 𝓓.𝓤
      strongMonoidal : StrongMonoidal F

    open Functor F public
    open StrongMonoidal strongMonoidal public

FlipSM
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
      {𝓒 : MonoidalCategory o₁ m₁ ℓ₁} {𝓓 : MonoidalCategory o₂ m₂ ℓ₂}
      {F : Functor (MonoidalCategory.𝓤 𝓒) (MonoidalCategory.𝓤 𝓓)}
  → StrongMonoidal 𝓒 𝓓 F → StrongMonoidal (FlipMC 𝓒) (FlipMC 𝓓) F
FlipSM {𝓒 = 𝓒} {𝓓} SMF =
  record
    { laxMonoidal = record
        { zip₀ = F.zip₀
        ; μ = wrapNT record { α = F.zip ; naturality = F.μ .naturality }
        ; associative =
            begin
              F.μ .α ∘ (-⊗- ₁$ F.μ .α , id) ∘ assocˡ

            ≈⟨ ∘-assocˡ ⟩
              (F.μ .α ∘ (-⊗- ₁$ F.μ .α , id)) ∘ assocˡ

            ≈˘⟨ transposeˡ⁻
                  (liftRetracts F.F (𝓒.assoc .inverse .right-inverse))
                  (≈.trans
                    (transposeʳ⁺
                      (assoc .inverse .left-inverse)
                      (≈.trans ∘-assocʳ F.associative))
                    ∘-assocʳ) ⟩
              F.map₁ 𝓒.assocˡ ∘ F.μ .α ∘ (-⊗- ₁$ id , F.μ .α)
            ∎
        ; unitalˡ = F.unitalʳ
        ; unitalʳ = F.unitalˡ
        }
    ; inv-zip₀ = F.inv-zip₀
    ; inv-zip = F.inv-zip
    }
  where
    module F = StrongMonoidalFunctor (bundle SMF)
    open MonoidalCategory 𝓓
    module 𝓒 = MonoidalCategory 𝓒
    open ≈-Reasoning
    open Categories.Inverse.In 𝓤 using (transposeˡ⁻; transposeʳ⁺)

FlipSMF
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
      {𝓒 : MonoidalCategory o₁ m₁ ℓ₁} {𝓓 : MonoidalCategory o₂ m₂ ℓ₂}
  → StrongMonoidalFunctor 𝓒 𝓓 → StrongMonoidalFunctor (FlipMC 𝓒) (FlipMC 𝓓)
FlipSMF (bundle SM) = bundle (FlipSM SM)
