module Categories.Syntax.Cartesian.Core where

-- The core module of datatypes and definitions for cartesian category
-- syntax over a polyquiver.  This module is not parameterized over
-- the PolyQuiver, so each datatype can be individually parameterized
-- over only the parts it needs.

open import Data.List as List using (List; [_]; _∷_; []; _++_)
open import Data.Product using (_×_; _,_)
open import Level using (Level)
import Function
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as ≡ using
  ( _≡_; refl
  ; cong; cong₂; trans; sym
  )

private
  variable
    o m : Level
    Type : Set o
    Mor : List Type → List Type → Set m

infixr 30 _⊗_

data Object (Type : Set o) : Set o where
  prim : Type → Object Type
  𝟏 : Object Type
  _⊗_ : (A B : Object Type) → Object Type

toList : Object Type → List Type
toList (prim A) = [ A ]
toList 𝟏 = []
toList (A ⊗ B) = toList A ++ toList B

toObj₁ : Type → List Type → Object Type
toObj₁ x₁ [] = prim x₁
toObj₁ x₁ (x₂ ∷ xs) = prim x₁ ⊗ toObj₁ x₂ xs

toObj : List Type → Object Type
toObj [] = 𝟏
toObj (x ∷ xs) = toObj₁ x xs

toList-toObj₁ : ∀ (A₁ : Type) As → toList (toObj₁ A₁ As) ≡ A₁ ∷ As
toList-toObj₁ A₁ [] = refl
toList-toObj₁ A₁ (A₂ ∷ As) = cong (A₁ ∷_) (toList-toObj₁ _ _)

toList-toObj : ∀ (As : List Type) → toList (toObj As) ≡ As
toList-toObj [] = refl
toList-toObj (A₁ ∷ As) = toList-toObj₁ A₁ As

toObj-transpose : ∀ (As : List Type) {A} → toObj As ≡ A → As ≡ toList A
toObj-transpose _ As≡A = trans (sym (toList-toObj _)) (cong toList As≡A)

-- toObj is an inverse of toList only for arguments of the form `toObj As`.
toObj-toList : ∀ (As : List Type) {A} → toObj As ≡ A → toObj (toList A) ≡ A
toObj-toList As As≡A = trans (sym (cong toObj (toObj-transpose As As≡A))) As≡A

prim-injective : ∀ {A₁ A₂ : Type} → prim A₁ ≡ prim A₂ → A₁ ≡ A₂
prim-injective refl = refl

⊗-injective
  : ∀ {A₁ A₂ B₁ B₂ : Object Type}
  → A₁ ⊗ B₁ ≡ A₂ ⊗ B₂ → A₁ ≡ A₂ × B₁ ≡ B₂
⊗-injective refl = refl , refl

toObj₁-injective
  : ∀ (A₁ B₁ : Type) (As Bs : List Type)
  → toObj₁ A₁ As ≡ toObj₁ B₁ Bs → A₁ ≡ B₁ × As ≡ Bs
toObj₁-injective A₁ B₁ [] [] refl = refl , refl
toObj₁-injective A₁ B₁ (A₂ ∷ As) (B₂ ∷ Bs) x =
  let (pA₁≡pB₁ , tA₂≡tB₂) = ⊗-injective x
      (A₂≡B₂ , As≡Bs) = toObj₁-injective _ _ _ _ tA₂≡tB₂
  in  prim-injective pA₁≡pB₁ , cong₂ _∷_ A₂≡B₂ As≡Bs

toObj-injective : ∀ (As Bs : List Type) → toObj As ≡ toObj Bs → As ≡ Bs
toObj-injective [] [] x = refl
toObj-injective (A₁ ∷ As) (B₁ ∷ Bs) x =
  let (y , z) = toObj₁-injective A₁ B₁ As Bs x
  in  cong₂ _∷_ y z
toObj-injective [] (_ ∷ []) ()
toObj-injective [] (_ ∷ _ ∷ _) ()
toObj-injective (_ ∷ []) [] ()
toObj-injective (_ ∷ _ ∷ _) [] ()

data Morphism {Type : Set o} (Mor : List Type → List Type → Set m) : (A B : Object Type) → Set (o ⊔ m)
    where
  prim : ∀ {As Bs} → Mor As Bs → Morphism Mor (toObj As) (toObj Bs)
  id : ∀ {A} → Morphism Mor A A
  _∘_ : ∀ {A B C} → Morphism Mor B C → Morphism Mor A B → Morphism Mor A C
  _△_ : ∀ {A B C} → Morphism Mor A B → Morphism Mor A C → Morphism Mor A (B ⊗ C)
  p₁ : ∀ {A B} → Morphism Mor (A ⊗ B) A
  p₂ : ∀ {A B} → Morphism Mor (A ⊗ B) B
  ε : ∀ {A} → Morphism Mor A 𝟏
