{-# OPTIONS --safe #-}

module Categories.Category where

open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Unit using (⊤)
open import Function.Equality using (Π; _⟶_; _⇨_; _⟨$⟩_)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

record Category (o m ℓ : Level) : Set (suc (o ⊔ m ⊔ ℓ)) where
  infixr 40 _∘_
  infix 10 _≈_
  field
    Obj : Set o
    _⇒_ : (A B : Obj) → Set m
    _≈_ : ∀ {A B} → Rel (A ⇒ B) ℓ

    id : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

    equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})

    -- N.B. ∘ is \o but also \comp, which behaves better when followed by a hyphen.
    ∘-resp-≈
      : ∀ {A B C} {f₁ f₂ : B ⇒ C} {g₁ g₂ : A ⇒ B}
      → f₁ ≈ f₂ → g₁ ≈ g₂ → f₁ ∘ g₁ ≈ f₂ ∘ g₂

    ∘-idˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    ∘-idʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    ∘-assocˡ
      : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
      → f ∘ g ∘ h ≈ (f ∘ g) ∘ h

  setoid : ∀ {A B : Obj} → Setoid m ℓ
  setoid {A} {B} = record { Carrier = A ⇒ B ; _≈_ = _≈_ ; isEquivalence = equiv }

  module ≈ {A B} = IsEquivalence (equiv {A} {B})
  module ≈-Reasoning {A B} = SetoidReasoning (setoid {A} {B})

  ∘-resp-≈ˡ
    : ∀ {A B C} {f₁ f₂ : B ⇒ C} {g : A ⇒ B}
    → f₁ ≈ f₂ → f₁ ∘ g ≈ f₂ ∘ g
  ∘-resp-≈ˡ f₁≈f₂ = ∘-resp-≈ f₁≈f₂ ≈.refl

  ∘-resp-≈ʳ
    : ∀ {A B C} {f : B ⇒ C} {g₁ g₂ : A ⇒ B}
    → g₁ ≈ g₂ → f ∘ g₁ ≈ f ∘ g₂
  ∘-resp-≈ʳ = ∘-resp-≈ ≈.refl

  ∘-assocʳ
    : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
    → (f ∘ g) ∘ h ≈ f ∘ g ∘ h
  ∘-assocʳ = ≈.sym ∘-assocˡ

  -- Convenience aliases for reassociating and focusing on the
  -- newly-composed stuff in one step.
  ∘∘-resp-≈ˡ
    : ∀ {A B C D}
        {f : B ⇒ C} {g : A ⇒ B} {h : A ⇒ C} {i : D ⇒ A}
    → f ∘ g ≈ h
    → f ∘ g ∘ i ≈ h ∘ i
  ∘∘-resp-≈ˡ f∘g≈h = ≈.trans ∘-assocˡ (∘-resp-≈ˡ f∘g≈h)

  ∘∘-resp-≈ʳ
    : ∀ {A B C D}
        {f : B ⇒ C} {g : A ⇒ B} {h : A ⇒ C} {i : C ⇒ D}
    → f ∘ g ≈ h
    → (i ∘ f) ∘ g ≈ i ∘ h
  ∘∘-resp-≈ʳ f∘g≈h = ≈.trans ∘-assocʳ (∘-resp-≈ʳ f∘g≈h)

_[_⇒_] : ∀ {o m ℓ} (𝓒 : Category o m ℓ) (A B : Category.Obj 𝓒) → Set m
_[_⇒_] = Category._⇒_

_[_∘_]
  : ∀ {o m ℓ} (𝓒 : Category o m ℓ) {A B C : Category.Obj 𝓒}
      (f : 𝓒 [ B ⇒ C ]) (g : 𝓒 [ A ⇒ B ])
  → 𝓒 [ A ⇒ C ]
_[_∘_] = Category._∘_

_[_≈_] : ∀ {o m ℓ} (𝓒 : Category o m ℓ) {A B : Category.Obj 𝓒} (f g : 𝓒 [ A ⇒ B ]) → Set ℓ
_[_≈_] = Category._≈_

_[_⊜_]
  : ∀ {o m ℓ} (𝓒 : Category o m ℓ) {A B : Category.Obj 𝓒}
      {f g h : 𝓒 [ A ⇒ B ]}
  → 𝓒 [ g ≈ h ]
  → 𝓒 [ f ≈ g ]
  → 𝓒 [ f ≈ h ]
𝓒 [ g≈h ⊜ f≈g ] = Category.≈.trans 𝓒 f≈g g≈h

-- Build a category out of an existing hom-setoid family.
setoidCategory
  : ∀ {o m ℓ} {Obj : Set o}
  → (hom : ∀ (A B : Obj) → Setoid m ℓ)
  → (id : ∀ {A} → Setoid.Carrier (hom A A))
  → (compose : ∀ {A B C} → hom B C ⟶ hom A B ⇨ hom A C)
  -- Well, this isn't looking so tidy anymore...
  → (∀ {A B} {f : Setoid.Carrier (hom A B)} → Setoid._≈_ (hom A B) (compose ⟨$⟩ id ⟨$⟩ f) f)
  → (∀ {A B} {f : Setoid.Carrier (hom A B)} → Setoid._≈_ (hom A B) (compose ⟨$⟩ f ⟨$⟩ id) f)
  → (∀ {A B C D}
       {f : Setoid.Carrier (hom C D)}
       {g : Setoid.Carrier (hom B C)}
       {h : Setoid.Carrier (hom A B)}
     → Setoid._≈_ (hom A D)
       (compose ⟨$⟩ f ⟨$⟩ (compose ⟨$⟩ g ⟨$⟩ h))
       (compose ⟨$⟩ (compose ⟨$⟩ f ⟨$⟩ g) ⟨$⟩ h))
  → Category o m ℓ
setoidCategory {Obj = Obj} hom id compose ∘-idˡ ∘-idʳ ∘-assocˡ = record
  { id = id
  ; equiv = λ {A} {B} → Setoid.isEquivalence (hom A B)
  ; ∘-resp-≈ = λ f₁≈f₂ g₁≈g₂ → Π.cong compose f₁≈f₂ g₁≈g₂
  ; ∘-idˡ = ∘-idˡ
  ; ∘-idʳ = ∘-idʳ
  ; ∘-assocˡ = ∘-assocˡ
  -- The rest implied by equiv and ∘-resp-≈
  }

-- A stripped-down category without equivalence laws, for use in type
-- parameters of records.  Using full-fledged categories as parameters
-- can require Agda to normalize and unify the entirety of all the
-- proofs when type-checking, so making records indexed by only the
-- fields that directly affect the field types reduces needless and
-- time-consuming work.
record RawCategory o m ℓ : Set (suc (o ⊔ m ⊔ ℓ)) where
  field
    Obj : Set o
    _⇒_ : (A B : Obj) → Set m
    _≈_ : ∀ {A B} (f g : A ⇒ B) → Set ℓ
    id : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} (f : B ⇒ C) (g : A ⇒ B) → A ⇒ C

toRawCategory : ∀ {o m ℓ} → Category o m ℓ → RawCategory o m ℓ
toRawCategory 𝓒 = record
  { Obj = Category.Obj 𝓒
  ; _⇒_ = Category._⇒_ 𝓒
  ; _≈_ = Category._≈_ 𝓒
  ; id = Category.id 𝓒
  ; _∘_ = Category._∘_ 𝓒
  }
