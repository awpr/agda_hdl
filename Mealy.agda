{-# OPTIONS --sized-types #-}

module Mealy where

open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (case_of_)
open import Level using (Level; _⊔_; suc)
open import Size using (Size; ∞)
open import Codata.Thunk using (Thunk; force)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

open import Categories.Bicartesian using (Bicartesian)
open import Categories.Category using (Category)
open import Categories.Cartesian using (Cartesian)
open import Categories.CausalLoop using (Causal)
open import Categories.Coproducts using (Coproducts)
open import Categories.Distributive using (Distributive; DistributiveCategory; bundle)
open import Categories.Terminal using (TerminalObject)

mutual
  -- A Mealy machine serving as the semantics of a digital circuit.
  --
  -- Given an `A` input for the present cycle, it produces a `B` output
  -- and a "next" Mealy machine (with, presumably, updated internal
  -- state).
  record Mealy {a b} (A : Set a) (B : Set b) (i : Size) : Set (a ⊔ b) where
    coinductive
    field
      step : A → MealyResult A B i

  record MealyResult {a b} (A : Set a) (B : Set b) (i : Size) : Set (a ⊔ b) where
    constructor _,_
    -- Not sure if this mix of inductive and coinductive is actually
    -- okay or if I've just confused Agda into accepting it, but it
    -- seems to be behaving how I want so far.
    inductive
    pattern
    field
      output : B
      next : Thunk (Mealy A B) i

open Mealy public using (step)

open MealyResult public using (output; next)

mutual
  record MealyEquiv
      {a b} {A : Set a} {B : Set b}
      (x y : Mealy A B ∞) (i : Size)
      : Set (a ⊔ b)
      where
    coinductive
    field
      step : (z : A) → MealyResultEquiv (x .step z) (y .step z) i

  record MealyResultEquiv
      {a b} {A : Set a} {B : Set b}
      (x y : MealyResult A B ∞) (i : Size)
      : Set (a ⊔ b)
      where
    constructor _,_
    inductive
    pattern
    field
      output : x .output ≡ y .output
      next : Thunk (MealyEquiv (x .next .force) (y .next .force)) i

open MealyEquiv public using (step)
open MealyResultEquiv public using (output; next)

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    i : Size

_≈_ : (f g : Mealy A B ∞) → Set _
f ≈ g = MealyEquiv f g ∞

≈-refl : ∀ {x : Mealy A B ∞} {i} → MealyEquiv x x i
≈-refl .step z = record { output = refl ; next = λ where .force → ≈-refl }

≈-sym : ∀ {x y : Mealy A B ∞} {i} → MealyEquiv x y i → MealyEquiv y x i
≈-sym x≈y .step z =
  let ox≡oy , x≈y′ = x≈y .step z
  in  ≡.sym ox≡oy , λ where .force → ≈-sym (x≈y′ .force)

≈-trans
  : ∀ {x y z : Mealy A B ∞} {i}
  → MealyEquiv x y i
  → MealyEquiv y z i
  → MealyEquiv x z i
≈-trans x≈y y≈z .step w =
  let ox≡oy , x≈y′ = x≈y .step w
      oy≡oz , y≈z′ = y≈z .step w
  in  ≡.trans ox≡oy oy≡oz , λ where .force → ≈-trans (x≈y′ .force) (y≈z′ .force)

≈-equiv : IsEquivalence (λ x y → MealyEquiv {A = A} {B} x y i)
≈-equiv = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

id : Mealy A A i
id .step x = x , λ where .force → id

infixr 20 _∘_
_∘_ : Mealy B C i → Mealy A B i → Mealy A C i
(f ∘ g) .step x =
  let x′ , g′ = g .step x
      x″ , f′ = f .step x′
  in  x″ , λ where .force → f′ .force ∘ g′ .force

∘-resp-≈
  : ∀ {f₁ f₂ : Mealy B C ∞} {g₁ g₂ : Mealy A B ∞}
  → MealyEquiv f₁ f₂ i
  → MealyEquiv g₁ g₂ i
  → MealyEquiv (f₁ ∘ g₁) (f₂ ∘ g₂) i
∘-resp-≈ {f₁ = f₁} {g₂ = g₂} f₁≈f₂ g₁≈g₂ .step z =
  let og₁≡og₂ , g₁≈g₂′ = g₁≈g₂ .step z
      of₁≡of₂ , f₁≈f₂′ = f₁≈f₂ .step (g₂ .step z .output)
  in  record
        { output = ≡.trans (≡.cong (λ x → f₁ .step x .output) og₁≡og₂) of₁≡of₂
        ; next = λ where
            .force {j} →
              ∘-resp-≈
                (≡.subst
                  (λ x → MealyEquiv (f₁ .step x .next .force) _ j)
                  (≡.sym og₁≡og₂)
                  (f₁≈f₂′ .force))
                (g₁≈g₂′ .force)
        }

∘-idˡ : ∀ {f : Mealy A B ∞} → MealyEquiv (id ∘ f) f i
∘-idˡ .step x = refl , λ where .force → ∘-idˡ

∘-idʳ : ∀ {f : Mealy A B ∞} → MealyEquiv (f ∘ id) f i
∘-idʳ .step x = refl , λ where .force → ∘-idʳ

∘-assocˡ
  : ∀ {f : Mealy C D ∞} {g : Mealy B C ∞} {h : Mealy A B ∞}
  → MealyEquiv (f ∘ g ∘ h) ((f ∘ g) ∘ h) i
∘-assocˡ .step x = refl , λ where .force → ∘-assocˡ

category : ∀ {ℓ} → Category (suc ℓ) ℓ ℓ
category {ℓ} = record
  { Obj = Set ℓ
  ; _⇒_ = λ A B → Mealy A B ∞
  ; _≈_ = λ x y → MealyEquiv x y ∞
  ; id = id
  ; _∘_ = _∘_
  ; equiv = ≈-equiv
  ; ∘-resp-≈ = ∘-resp-≈
  ; ∘-idˡ = ∘-idˡ
  ; ∘-idʳ = ∘-idʳ
  ; ∘-assocˡ = ∘-assocˡ
  }

const : B → Mealy A B i
const x .step _ = x , λ where .force → const x

ε : Mealy {b = b} A ⊤ i
ε = const tt

ε-unique : ∀ {f : Mealy {b = b} A ⊤ ∞} → MealyEquiv f ε i
ε-unique .step _ = refl , λ where .force → ε-unique

terminal : ∀ {ℓ} → TerminalObject (category {ℓ})
terminal = record
  { ⋆ = ⊤
  ; ε = const tt
  ; ε-unique = ε-unique
  }

map : (A → B) → Mealy A B i
map f .step x = f x , λ where .force → map f

_△_ : Mealy A B i → Mealy A C i → Mealy A (B × C) i
(f △ g) .step x =
  let fx , f′ = f .step x
      gx , g′ = g .step x
  in  (fx , gx) , λ where .force → f′ .force △ g′ .force

△-factors-p₁
  : ∀ {f : Mealy A B ∞} {g : Mealy A C ∞}
  → MealyEquiv (map proj₁ ∘ (f △ g)) f i
△-factors-p₁ .step x = refl , λ where .force → △-factors-p₁

△-factors-p₂
  : ∀ {f : Mealy A B ∞} {g : Mealy A C ∞}
  → MealyEquiv (map proj₂ ∘ (f △ g)) g i
△-factors-p₂ .step x = refl , λ where .force → △-factors-p₂

△-unique
  : ∀ {f : Mealy A B ∞} {g : Mealy A C ∞} {f△g : Mealy A (B × C) ∞}
  → MealyEquiv (map proj₁ ∘ f△g) f i
  → MealyEquiv (map proj₂ ∘ f△g) g i
  → MealyEquiv f△g (f △ g) i
△-unique p₁≈f p₂≈g .step x =
  let p₁≡fx , p₁≈f′ = p₁≈f .step x
      p₂≡gx , p₂≈g′ = p₂≈g .step x
  in  ≡.cong₂ _,_ p₁≡fx p₂≡gx ,
        λ where .force → △-unique (p₁≈f′ .force) (p₂≈g′ .force)

cartesian : ∀ {ℓ} → Cartesian (category {ℓ})
cartesian = record
  { terminal = terminal
  ; _×_ = _×_
  ; _△_ = _△_
  ; p₁ = map proj₁
  ; p₂ = map proj₂
  ; △-factors-p₁ = △-factors-p₁
  ; △-factors-p₂ = △-factors-p₂
  ; △-unique = △-unique
  }

_▽_ : Mealy A C i → Mealy B C i → Mealy (A ⊎ B) C i
(f ▽ g) .step (inj₁ x) =
  let fx , f′ = f .step x
  in  fx , λ where .force → f′ .force ▽ g
(f ▽ g) .step (inj₂ x) =
  let gx , g′ = g .step x
  in  gx , λ where .force → f ▽ g′ .force

▽-resp-≈
  : ∀ {f₁ f₂ : Mealy A C ∞} {g₁ g₂ : Mealy B C ∞}
  → MealyEquiv f₁ f₂ i → MealyEquiv g₁ g₂ i → MealyEquiv (f₁ ▽ g₁) (f₂ ▽ g₂) i
▽-resp-≈ f₁≈f₂ g₁≈g₂ .step (inj₁ x) =
  let f₁x≡f₂x , f₁≈f₂′ = f₁≈f₂ .step x
  in  f₁x≡f₂x , λ where .force → ▽-resp-≈ (f₁≈f₂′ .force) g₁≈g₂
▽-resp-≈ f₁≈f₂ g₁≈g₂ .step (inj₂ x) =
  let g₁x≡g₂x , g₁≈g₂′ = g₁≈g₂ .step x
  in  g₁x≡g₂x , λ where .force → ▽-resp-≈ f₁≈f₂ (g₁≈g₂′ .force)

coproducts : ∀ {ℓ} → Coproducts (category {ℓ})
coproducts = record
  { _∐_ = _⊎_
  ; ⊥ = ⊥
  ; ∃! = map ⊥-elim
  ; i₁ = map inj₁
  ; i₂ = map inj₂
  ; _▽_ = _▽_
  ; ▽-resp-≈ = ▽-resp-≈
  }

bicartesian : ∀ {ℓ} → Bicartesian (category {ℓ})
bicartesian = record
  { cartesian = cartesian
  ; coproducts = coproducts
  }

distʳ′ : Mealy ((A ⊎ B) × C) (A × C ⊎ B × C) i
distʳ′ = map λ
  { (inj₁ a , x) → inj₁ (a , x)
  ; (inj₂ b , x) → inj₂ (b , x)
  }

distributive : ∀ {ℓ} → Distributive (category {ℓ})
distributive = record
  { bicartesian = bicartesian
  ; distʳ = record { f⁻¹ = distʳ′ }
  }

MealyMachines : ∀ {ℓ} → DistributiveCategory (suc ℓ) ℓ ℓ
MealyMachines = bundle distributive

loop′
  : ∀ {s} {S : Set s}
  → S
  → Mealy (S × A) (S × B) i
  → Mealy A B i
loop′ s₀ f .step x =
  let (s₁ , y) , f′ = f .step (s₀ , x)
  in  y , (λ where .force → loop′ s₁ (f′ .force))

causal : ∀ {ℓ} → Causal (DistributiveCategory.monoidalCategory (MealyMachines {ℓ}))
causal = record { loop = λ s → loop′ (s .step tt .output) }

steps : Mealy A B ∞ → List A → List B × Mealy A B ∞
steps f [] = [] , f
steps f (x ∷ xs) =
  let fx , f′ = f .step x
      fxs , f″ = steps (f′ .force) xs
  in  (fx ∷ fxs) , f″
