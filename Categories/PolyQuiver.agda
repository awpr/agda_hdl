module Categories.PolyQuiver where

open import Data.List as List using (List; []; _∷_)
open import Data.List.Properties as List
open import Function using (_∘_; id)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Rel; REL; IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Extras as ≡ using
   ( _≡_; _≗_; refl
   ; cast; cong; cong₂; subst₂; sym
   )
import Relation.Binary.PropositionalEquality.Properties.Extras as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Cartesian using (CartesianCategory)

record PolyQuiver (o m ℓ : Level) : Set (suc (o ⊔ m ⊔ ℓ)) where
  field
    Type : Set o
    _⇒_ : List Type → List Type → Set m
    _≈_ : ∀ {As Bs} → Rel (As ⇒ Bs) ℓ

    equiv : ∀ {As Bs} → IsEquivalence (_≈_ {As} {Bs})

  setoid : ∀ {As Bs : List Type} → Setoid m ℓ
  setoid {As} {Bs} = record
    { Carrier = As ⇒ Bs
    ; _≈_ = _≈_
    ; isEquivalence = equiv
    }

  module ≈ {As} {Bs} = IsEquivalence (equiv {As} {Bs})
  module ≈-Reasoning {As} {Bs} = SetoidReasoning (setoid {As} {Bs} )

  subst₂-dist-≈
    : ∀ {As₁ As₂ Bs₁ Bs₂} {f g : As₁ ⇒ Bs₁}
    → (As₁≡As₂ : As₁ ≡ As₂)
    → (Bs₁≡Bs₂ : Bs₁ ≡ Bs₂)
    → subst₂ (λ _ _ → Set ℓ) As₁≡As₂ Bs₁≡Bs₂ (f ≈ g) ≡
        subst₂ _⇒_ As₁≡As₂ Bs₁≡Bs₂ f ≈ subst₂ _⇒_ As₁≡As₂ Bs₁≡Bs₂ g
  subst₂-dist-≈ refl refl = refl

private
  variable
    o₁ m₁ o₂ m₂ o₃ m₃ ℓ₁ ℓ₂ ℓ₃ : Level
    Q : PolyQuiver o₁ m₁ ℓ₁
    R : PolyQuiver o₂ m₂ ℓ₂
    S : PolyQuiver o₃ m₃ ℓ₃

record PQMorphism
    (Q : PolyQuiver o₁ m₁ ℓ₁)
    (R : PolyQuiver o₂ m₂ ℓ₂)
    : Set (o₁ ⊔ o₂ ⊔ m₁ ⊔ m₂ ⊔ ℓ₁ ⊔ ℓ₂)
    where
  private module Q = PolyQuiver Q
  private module R = PolyQuiver R

  field
    map₀ : Q.Type → R.Type
    map₁ : ∀ {As Bs} → As Q.⇒ Bs → List.map map₀ As R.⇒ List.map map₀ Bs

    map₁-resp-≈ : ∀ {As Bs} {f g : As Q.⇒ Bs} → f Q.≈ g → map₁ f R.≈ map₁ g

_∘M_ : PQMorphism R S → PQMorphism Q R → PQMorphism Q S
_∘M_ {S = S} {Q = Q} M₁ M₂ = record
  { map₀ = M₁.map₀ ∘ M₂.map₀
  ; map₁ = map₁
  ; map₁-resp-≈ = map₁-resp-≈
  }
 where
  module M₁ = PQMorphism M₁
  module M₂ = PQMorphism M₂
  module Q = PolyQuiver Q
  module S = PolyQuiver S

  map₁
    : ∀ {As Bs}
    → (f : As Q.⇒ Bs)
    → List.map (M₁.map₀ ∘ M₂.map₀) As S.⇒ List.map (M₁.map₀ ∘ M₂.map₀) Bs
  map₁ {As} {Bs} =
    subst₂ (PolyQuiver._⇒_ S)
      (sym (List.map-compose As))
      (sym (List.map-compose Bs)) ∘
    M₁.map₁ ∘
    M₂.map₁

  map₁-resp-≈
    : ∀ {As Bs} {f g : As Q.⇒ Bs}
    → f Q.≈ g
    → map₁ f S.≈ map₁ g
  map₁-resp-≈ {As} {Bs} {f} {g} f≈g = cast
    (begin
        M₁.map₁ (M₂.map₁ f) S.≈ M₁.map₁ (M₂.map₁ g)

      ≡˘⟨ ≡.subst₂-dist₀ ⟩
        subst₂ (λ _ _ → Set _)
          (sym (List.map-compose As))
          (sym (List.map-compose Bs))
          (M₁.map₁ (M₂.map₁ f) S.≈ M₁.map₁ (M₂.map₁ g))

      ≡⟨ S.subst₂-dist-≈ _ _ ⟩
        subst₂ S._⇒_
          (sym (List.map-compose As))
          (sym (List.map-compose Bs))
          (M₁.map₁ (M₂.map₁ f))
          S.≈
        subst₂ S._⇒_
          (sym (List.map-compose As))
          (sym (List.map-compose Bs))
          (M₁.map₁ (M₂.map₁ g))

      ≡⟨⟩
        map₁ f S.≈ map₁ g
      ∎)
    (M₁.map₁-resp-≈ (M₂.map₁-resp-≈ f≈g))
    where
      open ≡.≡-Reasoning

module _ (CC : CartesianCategory o₁ m₁ ℓ₁) where
  private module C = CartesianCategory CC

  toCCObj₁ : C.Obj → List C.Obj → C.Obj
  toCCObj₁ x [] = x
  toCCObj₁ x₁ (x₂ ∷ xs) = x₁ C.× toCCObj₁ x₂ xs

  toCCObj : List C.Obj → C.Obj
  toCCObj [] = C.⋆
  toCCObj (x ∷ xs) = toCCObj₁ x xs

  record WrappedCC (As Bs : List C.Obj) : Set m₁ where
    constructor wrap
    field
      unwrap : toCCObj As C.⇒ toCCObj Bs

  Wrapped≈ : ∀ {ℓ} → (∀ {A B} → Rel (A C.⇒ B) ℓ) → ∀ {As Bs} → Rel (WrappedCC As Bs) ℓ
  Wrapped≈ _≈_ (wrap f) (wrap g) = f ≈ g

  ccToPolyQuiver : PolyQuiver o₁ m₁ ℓ₁
  ccToPolyQuiver = record
    { Type = C.Obj
    ; _⇒_ = WrappedCC
    ; _≈_ = Wrapped≈ C._≈_
    ; equiv = record { refl = C.≈.refl ; sym = C.≈.sym ; trans = C.≈.trans }
    }
