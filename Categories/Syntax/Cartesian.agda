open import Categories.PolyQuiver using (PolyQuiver)

module Categories.Syntax.Cartesian {o m ℓ} (Q : PolyQuiver o m ℓ) where

open import Data.Empty using (⊥)
open import Data.List as List using (List; _∷_; []; [_]; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
import Function
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality.Extras as ≡ using
  ( _≡_; refl; _≗_; cast
  ; sym; trans; cong; cong₂; subst₂
  )
import Relation.Binary.PropositionalEquality.Properties.Extras as ≡

open import Categories.Cartesian using (Cartesian; CartesianCategory)
open import Categories.Category using (Category)
open import Categories.Category.Types using (→CC′)
open import Categories.Functor using (Functor)
open import Categories.Terminal using (TerminalObject)

open import Categories.Syntax.Cartesian.Core
  hiding (Morphism; Object)
  public
open import Categories.Syntax.Cartesian.Core
  using (Morphism; Object)

private module Q = PolyQuiver Q

open Q using (Type) renaming (_⇒_ to Mor) public

Obj : Set o
Obj = Object Type

infixr 10 _⇒_
_⇒_ : (A B : Object Type) → Set (o ⊔ m)
_⇒_ = Morphism Mor

infixr 20 _∘_

-- TODO: it's confusing that PolyQuiver has an _⇒_ field yet Syntax
-- also has _⇒_ and we often say `module Q = Syntax Q`, so Q._⇒_
-- sometimes means the underlying polyquiver morphisms and sometimes
-- means the syntax morphisms.  Find some way to fix this confusion.

-- Lemmas for distributing substitution over each constructor of _⇒_.
-- These turn up when trying to prove equivalence of morphisms with
-- equal but not syntactically-equal types.

subst₂-dist-prim
  : ∀ {As₁ As₂ Bs₁ Bs₂}
      (As₁≡As₂ : As₁ ≡ As₂)
      (Bs₁≡Bs₂ : Bs₁ ≡ Bs₂)
      {f : Mor As₁ Bs₁}
  → subst₂ _⇒_ (cong toObj As₁≡As₂) (cong toObj Bs₁≡Bs₂) (prim f) ≡
      prim (subst₂ Mor As₁≡As₂ Bs₁≡Bs₂ f)
subst₂-dist-prim refl refl = refl

subst₂-dist-id
  : ∀ {A₁ A₂ : Obj}
      (A₁≡A₂ : A₁ ≡ A₂)
  → subst₂ _⇒_ A₁≡A₂ A₁≡A₂ id ≡ id
subst₂-dist-id refl = refl

subst₂-dist-∘
  : ∀ {A₁ A₂ B₁ B₂ C₁ C₂ : Obj}
      (A₁≡A₂ : A₁ ≡ A₂)
      (B₁≡B₂ : B₁ ≡ B₂)
      (C₁≡C₂ : C₁ ≡ C₂)
      {f g}
  → subst₂ _⇒_ A₁≡A₂ C₁≡C₂ (f ∘ g) ≡
      subst₂ _⇒_ B₁≡B₂ C₁≡C₂ f ∘ subst₂ _⇒_ A₁≡A₂ B₁≡B₂ g
subst₂-dist-∘ refl refl refl = refl

subst₂-dist-△
  : ∀ {A₁ A₂ B₁ B₂ C₁ C₂ : Obj}
      (A₁≡A₂ : A₁ ≡ A₂)
      (B₁≡B₂ : B₁ ≡ B₂)
      (C₁≡C₂ : C₁ ≡ C₂)
      {f g}
  → subst₂ _⇒_ A₁≡A₂ (cong₂ _⊗_ B₁≡B₂ C₁≡C₂) (f △ g) ≡
      subst₂ _⇒_ A₁≡A₂ B₁≡B₂ f △ subst₂ _⇒_ A₁≡A₂ C₁≡C₂ g
subst₂-dist-△ refl refl refl = refl

subst₂-dist-p₁
  : ∀ {A₁ A₂ B₁ B₂ : Obj}
      (A₁≡A₂ : A₁ ≡ A₂)
      (B₁≡B₂ : B₁ ≡ B₂)
  → subst₂ _⇒_ (cong₂ _⊗_ A₁≡A₂ B₁≡B₂) (A₁≡A₂) p₁ ≡ p₁
subst₂-dist-p₁ refl refl = refl

subst₂-dist-p₂
  : ∀ {A₁ A₂ B₁ B₂ : Obj}
      (A₁≡A₂ : A₁ ≡ A₂)
      (B₁≡B₂ : B₁ ≡ B₂)
  → subst₂ _⇒_ (cong₂ _⊗_ A₁≡A₂ B₁≡B₂) (B₁≡B₂) p₂ ≡ p₂
subst₂-dist-p₂ refl refl = refl

subst₂-dist-ε
  : ∀ {A₁ A₂ : Obj}
      (A₁≡A₂ : A₁ ≡ A₂)
  → subst₂ _⇒_ A₁≡A₂ refl ε ≡ ε
subst₂-dist-ε refl = refl

-- Lifting of relations on Q._⇒_ to _⇒_, augmented with additional
-- equivalences required by category structures: Pointwise R f g holds
-- if the _⇒_ constructors of f and g are equal and the "leaves"
-- inside prim are related by R, or if cartesian category laws require
-- it.
data Pointwise
    {ℓ} (R : ∀ {As Bs} → Rel (As Q.⇒ Bs) ℓ)
    : ∀ {A B} → A ⇒ B → A ⇒ B → Set (o ⊔ m ⊔ ℓ)
    where
  prim : ∀ {As Bs} {f g : As Q.⇒ Bs} → R f g → Pointwise R (prim f) (prim g)
  id : ∀ {A} → Pointwise R {A} id id
  _∘_
    : ∀ {A B C} {f₁ : B ⇒ C} {g₁ : A ⇒ B} {f₂ g₂}
    → Pointwise R f₁ f₂ → Pointwise R g₁ g₂ → Pointwise R (f₁ ∘ g₁) (f₂ ∘ g₂)

  △-factors-p₁ : ∀ {A B C} {f : A ⇒ B} {g : A ⇒ C} → Pointwise R (p₁ ∘ (f △ g)) f
  △-factors-p₂ : ∀ {A B C} {f : A ⇒ B} {g : A ⇒ C} → Pointwise R (p₂ ∘ (f △ g)) g
  △-unique
    : ∀ {A B C} {f : A ⇒ B} {g : A ⇒ C} {f△g : A ⇒ B ⊗ C}
    → Pointwise R (p₁ ∘ f△g) f
    → Pointwise R (p₂ ∘ f△g) g
    → Pointwise R f△g (f △ g)
  p₁ : ∀ {A B} → Pointwise R {A ⊗ B} {A} p₁ p₁
  p₂ : ∀ {A B} → Pointwise R {A ⊗ B} {B} p₂ p₂
  ε-unique : ∀ {A} {f : A ⇒ 𝟏} → Pointwise R {A} f ε


  ≈-sym : ∀ {A B} {f g : A ⇒ B} → Pointwise R f g → Pointwise R g f
  ≈-trans : ∀ {A B} {f g h : A ⇒ B} → Pointwise R f g → Pointwise R g h → Pointwise R f h

  ∘-idˡ : ∀ {A B} {f : A ⇒ B} → Pointwise R (id ∘ f) f
  ∘-idʳ : ∀ {A B} {f : A ⇒ B} → Pointwise R (f ∘ id) f
  ∘-assocˡ
    : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
    → Pointwise R (f ∘ g ∘ h) ((f ∘ g) ∘ h)

△-resp-≈
  : ∀ {r} {R : ∀ {As Bs} → Rel (Mor As Bs) r}
      {A B C} {f₁ : A ⇒ B} {g₁ : A ⇒ C} {f₂ g₂}
  → Pointwise R f₁ f₂ → Pointwise R g₁ g₂ → Pointwise R (f₁ △ g₁) (f₂ △ g₂)
△-resp-≈ f₁≈f₂ g₁≈g₂ = △-unique (≈-trans △-factors-p₁ f₁≈f₂) (≈-trans △-factors-p₂ g₁≈g₂)

Pointwise-refl
  : ∀ {r} {_≈_ : ∀ {As Bs} → Rel (Mor As Bs) r}
  → (∀ {As Bs} {f : Mor As Bs} → f ≈ f)
  → ∀ {A B} {f : A ⇒ B} → Pointwise _≈_ f f
Pointwise-refl ≈-refl {f = prim _} = prim ≈-refl
Pointwise-refl ≈-refl {f = id} = id
Pointwise-refl ≈-refl {f = _ ∘ _} = Pointwise-refl ≈-refl ∘ Pointwise-refl ≈-refl
Pointwise-refl ≈-refl {f = _ △ _} =
  △-resp-≈ (Pointwise-refl ≈-refl) (Pointwise-refl ≈-refl)
Pointwise-refl ≈-refl {f = p₁} = p₁
Pointwise-refl ≈-refl {f = p₂} = p₂
Pointwise-refl ≈-refl {f = ε} = ε-unique

≡→Pointwise≡ : ∀ {A B} → {f g : A ⇒ B} → f ≡ g → Pointwise _≡_ f g
≡→Pointwise≡ refl = Pointwise-refl refl

_≈_ : ∀ {A B} → Rel (A ⇒ B) (o ⊔ m ⊔ ℓ)
_≈_ = Pointwise Q._≈_

≈-refl : ∀ {A B} {f : A ⇒ B} → f ≈ f
≈-refl = Pointwise-refl Q.≈.refl

≈-reflexive : ∀ {A B} {f g : A ⇒ B} → f ≡ g → f ≈ g
≈-reflexive refl = ≈-refl

⇒Cat : Category o (o ⊔ m) (o ⊔ m ⊔ ℓ)
⇒Cat = record
  { Obj = Obj
  ; _⇒_ = _⇒_
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_

  ; equiv = record
      { refl = Pointwise-refl Q.≈.refl
      ; sym = ≈-sym
      ; trans = ≈-trans
      }

  ; ∘-resp-≈ = _∘_
  ; ∘-idˡ = ∘-idˡ
  ; ∘-idʳ = ∘-idʳ
  ; ∘-assocˡ = ∘-assocˡ
  }

term⇒ : TerminalObject ⇒Cat
term⇒ = record
  { ⋆ = 𝟏
  ; ε = ε
  ; ε-unique = ε-unique
  }

cart⇒ : Cartesian ⇒Cat
cart⇒ = record
  { terminal = term⇒
  ; _×_ = _⊗_
  ; _△_ = _△_
  ; p₁ = p₁
  ; p₂ = p₂
  ; △-factors-p₁ = △-factors-p₁
  ; △-factors-p₂ = △-factors-p₂
  ; △-unique = △-unique
  }

⇒CC : CartesianCategory o (o ⊔ m) (o ⊔ m ⊔ ℓ)
⇒CC = record { 𝓤 = ⇒Cat ; cartesian = cart⇒ }

open CartesianCategory ⇒CC
  using ()
  renaming
    ( monoidalCategory to ⇒MC; braidedMonoidalCategory to ⇒SMC
    ; monoidal to mon⇒; braided to braid⇒
    )
  public
