module Categories.Category.Setoids where

open import Level using (Level; suc; _⊔_; Lift; lift)

open import Categories.Cartesian using (Cartesian)
open import Categories.CartesianClosed using (CartesianClosed; CartesianClosedCategory)
open import Categories.Category using (Category; setoidCategory)
open import Categories.Monoidal using (Monoidal)
open import Categories.Terminal using (TerminalObject)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Function.Equality using (Π; _⟶_; id; _∘_; _⇨_; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as Trivial
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
import Relation.Binary.PropositionalEquality.Properties as ≡

private
  variable
    c c₁ c₂ c₃ c₄ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Setoid c₁ ℓ₁
    B : Setoid c₂ ℓ₂
    C : Setoid c₃ ℓ₃
    D : Setoid c₄ ℓ₄

curry′ : (×-setoid A B ⟶ C) → (A ⟶ B ⇨ C)
curry′ {A = A} f = record
  { _⟨$⟩_ = λ x → record
      { _⟨$⟩_ = λ y → f ⟨$⟩ (x , y)
      ; cong = λ y₁≈y₂ → Π.cong f (Setoid.refl A , y₁≈y₂)
      }
  ; cong = λ x₁≈x₂ y₁≈y₂ → Π.cong f (x₁≈x₂ , y₁≈y₂)
  }

curry : (×-setoid A B ⇨ C) ⟶ (A ⇨ B ⇨ C)
curry = record
  { _⟨$⟩_ = curry′
  ; cong = λ f₁≈f₂ x₁≈x₂ y₁≈y₂ → f₁≈f₂ (x₁≈x₂ , y₁≈y₂)
  }

uncurry′ : (A ⟶ B ⇨ C) → (×-setoid A B ⟶ C)
uncurry′ {C = C} f = record
  { _⟨$⟩_ = λ { (x , y) → f ⟨$⟩ x ⟨$⟩ y }
  ; cong = λ (x₁≈x₂ , y₁≈y₂) → Π.cong f x₁≈x₂ y₁≈y₂
  }

uncurry : (A ⇨ B ⇨ C) ⟶ (×-setoid A B ⇨ C)
uncurry = record
  { _⟨$⟩_ = uncurry′
  ; cong = λ f₁≈f₂ (x₁≈x₂ , y₁≈y₂) → f₁≈f₂ x₁≈x₂ y₁≈y₂
  }

swap : ×-setoid A B ⟶ ×-setoid B A
swap = record
  { _⟨$⟩_ = λ (x , y) → (y , x)
  ; cong = λ (x₁≈x₂ , y₁≈y₂) → y₁≈y₂ , x₁≈x₂
  }

curry₃′ : ×-setoid A (×-setoid B C) ⟶ D → A ⟶ B ⇨ C ⇨ D
curry₃′ f = (curry ∘_) $ curry ⟨$⟩ f

composition : (B ⇨ C) ⟶ (A ⇨ B) ⇨ (A ⇨ C)
-- Defining via `curry` means we define the `cong` once rather than
-- than defining forms with each prefix of the n-ary curried function
-- held constant.  (See the definition of `curry` for what defining a
-- curried function directly would look like).
composition = curry ⟨$⟩ record
  { _⟨$⟩_ = λ (f , g) → f ∘ g
  ; cong = λ (f₁≈f₂ , g₁≈g₂) → λ { x₁≈x₂ → f₁≈f₂ (g₁≈g₂ x₁≈x₂) }
    --                         ^ That's a load-bearing pat-lam.
    -- Otherwise (I think) all the inferred implicit arguments go up
    -- front like the following:
    --   ∀ {f₁,g₁} {f₂,g₂} {x₁} {x₂} f₁≈f₂,g₁≈g₂ x₁≈x₂
    --   → f₁ ⟨$⟩ g₁ ⟨$⟩ x₁ ≈ f₂ ⟨$⟩ g₂ ⟨$⟩ x₂
    --
    -- Yet the context demands that they be interleaved:
    --   ∀ {f₁,g₁} {f₂,g₂} f₁≈f₂,g₁≈g₂ {x₁} {x₂} x₁≈x₂
    --   → f₁ ⟨$⟩ g₁ ⟨$⟩ x₁ ≈ f₂ ⟨$⟩ g₂ ⟨$⟩ x₂
    --
    -- Making the outer lambda return a pattern-lambda creates a
    -- boundary that the inner implicit arguments can't float across,
    -- and puts them in the expected order.

  }

infixr 40 _∘⟶_
_∘⟶_ : B ⟶ C → A ⟶ B → A ⟶ C
f ∘⟶ g = composition ⟨$⟩ f ⟨$⟩ g

LiftSetoid : ∀ c₁ ℓ₁ → Setoid c ℓ → Setoid (c ⊔ c₁) (ℓ ⊔ ℓ₁)
LiftSetoid c₁ ℓ₁ s = record
  { Carrier = Lift c₁ (Setoid.Carrier s)
  ; _≈_ = λ (lift x) (lift y) → Lift ℓ₁ (Setoid._≈_ s x y)
  ; isEquivalence = record
      { refl = lift (Setoid.refl s)
      ; sym = λ (lift x) → lift (Setoid.sym s x)
      ; trans = λ (lift x) (lift y) → lift (Setoid.trans s x y)
      }
  }

liftSetoid : ∀ c₁ ℓ₁ {A : Setoid c ℓ} → A ⟶ LiftSetoid c₁ ℓ₁ A
liftSetoid _ _ = record { _⟨$⟩_ = lift ; cong = lift }

infix 10 _≈_
_≈_
  : ∀ {c₁ c₂ ℓ₁ ℓ₂} {A : Setoid c₁ ℓ₁} {B : Setoid c₂ ℓ₂}
  → (f g : A ⟶ B) → Set (c₁ ⊔ ℓ₁ ⊔ ℓ₂)
_≈_ {A = A} {B} = Setoid._≈_ (A ⇨ B)

∘-assocˡ
  : ∀ {c₁ c₂ c₃ c₄ ℓ₁ ℓ₂ ℓ₃ ℓ₄}
      {A : Setoid c₁ ℓ₁} {B : Setoid c₂ ℓ₂}
      {C : Setoid c₃ ℓ₃} {D : Setoid c₄ ℓ₄}
      {f : C ⟶ D} {g : B ⟶ C} {h : A ⟶ B}
  → f ∘⟶ g ∘⟶ h ≈ (f ∘⟶ g) ∘⟶ h
∘-assocˡ {f = f} {g} {h} x = Π.cong f (Π.cong g (Π.cong h x))

Setoids : ∀ c ℓ → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Setoids c ℓ = setoidCategory (_⇨_ {c} {ℓ}) id composition
  (λ {_} {_} {f} → Π.cong f)
  (λ {_} {_} {f} → Π.cong f)
  (λ {_} {_} {_} {_} {f} {g} {h} → ∘-assocˡ {f = f} {g} {h})

⋆ : ∀ {c ℓ} → Setoid c ℓ
⋆ {c} {ℓ} = LiftSetoid c ℓ (≡.setoid ⊤)

ε : ∀ {c ℓ} {A : Setoid c ℓ} → A ⟶ ⋆ {c} {ℓ}
ε = record { _⟨$⟩_ = λ _ → lift tt ; cong = λ _ → lift refl }

ε-unique : ∀ {c ℓ} {A : Setoid c ℓ} {f : A ⟶ ⋆} → f ≈ ε
ε-unique {f = f} {x} x≈y with lift tt ← f ⟨$⟩ x = lift refl

terminal : TerminalObject (Setoids c ℓ)
terminal {c} {ℓ} = record
  { ⋆ = ⋆
  ; ε = ε
  ; ε-unique = λ {A} {f} x≈y → ε-unique {f = f} x≈y
  }

pairing
  : ∀ {A : Setoid c₁ ℓ₁} {B : Setoid c₂ ℓ₂} {C : Setoid c₃ ℓ₃}
  → (A ⇨ B) ⟶ (A ⇨ C) ⇨ (A ⇨ ×-setoid B C)
pairing = curry₃′ $ record
  { _⟨$⟩_ = λ (f , g , x) → f ⟨$⟩ x , g ⟨$⟩ x
  ; cong = λ (f₁≈f₂ , g₁≈g₂ , x₁≈x₂) → f₁≈f₂ x₁≈x₂ , g₁≈g₂ x₁≈x₂
  }

cong²
  : (f : A ⟶ B ⇨ C)
  → ∀ {x₁ x₂ y₁ y₂}
  → Setoid._≈_ A x₁ x₂
  → Setoid._≈_ B y₁ y₂
  → Setoid._≈_ C (f ⟨$⟩ x₁ ⟨$⟩ y₁) (f ⟨$⟩ x₂ ⟨$⟩ y₂)
cong² f xx yy = Π.cong f xx yy

cartesian : Cartesian (Setoids c ℓ)
cartesian = record
  { terminal = terminal
  ; _×_ = ×-setoid
  ; _△_ = λ f g → pairing ⟨$⟩ f ⟨$⟩ g
  ; p₁ = record { _⟨$⟩_ = proj₁ ; cong = proj₁ }
  ; p₂ = record { _⟨$⟩_ = proj₂ ; cong = proj₂ }
  ; △-factors-p₁ = λ {_} {_} {_} {f} → Π.cong f
  ; △-factors-p₂ = λ {_} {_} {_} {_} {g} → Π.cong g
  ; △-unique = λ p₁≈f p₂≈g x≈y → p₁≈f x≈y , p₂≈g x≈y
  }

monoidal : Monoidal (Setoids c ℓ)
monoidal = Cartesian.monoidal cartesian

-- Only if the level of carriers is the same as the level of
-- equivalences, we can construct internal homs; thus `Setoids ℓ ℓ`.
cartesianClosed : CartesianClosed (Setoids ℓ ℓ)
cartesianClosed = record
  { cartesian = cartesian
  ; -↝- = record
      { map₀ = λ (A , B) → A ⇨ B
      ; map₁ = λ (f , g) → record
          { _⟨$⟩_ = λ h → g ∘ h ∘ f
          ; cong = λ h₁≈h₂ x₁≈x₂ → Π.cong g (h₁≈h₂ (Π.cong f x₁≈x₂))
          }
      ; map₁-resp-≈ = λ (f₁≈f₂ , g₁≈g₂) h₁≈h₂ x₁≈x₂ → g₁≈g₂ (h₁≈h₂ (f₁≈f₂ x₁≈x₂))
      ; map₁-id = Function.id
      ; map₁-∘ = λ
          { {_} {_} {_} {f = f₁ , f₂} {g = g₁ , g₂} f₁≈f₂ x≈y →
              Π.cong f₂ (Π.cong g₂ (f₁≈f₂ (Π.cong g₁ (Π.cong f₁ x≈y))))
          }
      }

  ; left-residual = record
      { left-adjunct = (_∘ swap) Function.∘ uncurry′
      ; right-adjunct = curry′ Function.∘ (_∘ swap)
      ; left-inverse = λ {_} {_} {f} xy₁≈xy₂ → Π.cong f xy₁≈xy₂
      ; right-inverse = λ {_} {_} {f} x₁≈x₂ y₁≈y₂ → Π.cong f x₁≈x₂ y₁≈y₂
      }

  ; right-residual = record
      { left-adjunct = uncurry′
      ; right-adjunct = curry′
      ; left-inverse = λ {_} {_} {f} xy₁≈xy₂ → Π.cong f xy₁≈xy₂
      ; right-inverse = λ {_} {_} {f} x₁≈x₂ y₁≈y₂ → Π.cong f x₁≈x₂ y₁≈y₂
      }

  ; curry-coherent = λ f x₁≈x₂ y₁≈y₂ → Π.cong f (x₁≈x₂ , y₁≈y₂)
  ; uncurry-coherent = λ f (x₁≈x₂ , y₁≈y₂) → Π.cong f x₁≈x₂ y₁≈y₂
  }

SetoidsCCC : ∀ ℓ → CartesianClosedCategory (suc ℓ) ℓ ℓ
SetoidsCCC ℓ = record { 𝓤 = Setoids ℓ ℓ ; cartesianClosed = cartesianClosed }
