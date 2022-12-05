module Experiments.Signatures.Unityped where

-- A PolyQuiver consisting of just a single bit type and basic logic
-- gate operations over it.

open import Data.List as List using (List; _∷_; []; [_])
import Data.Product
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

open import Categories.Cartesian using (CartesianCategory)
open import Categories.Category.Types using (→CC′; →Cat)
open import Categories.Functor using (Functor; _○_)
import Categories.Gel.Cartesian as Gel
open import Categories.PolyQuiver
import Categories.Syntax.Cartesian as Syntax
open import Categories.Syntax.Cartesian.Functors using (flatten; mapSyntax)

open import Data.Bit as Bit using (Bit; one; zero; _∧_; _∨_; _⊕_)
open import Data.Bit.Properties using (⊕-assoc)
open import Data.Finite using ()
open import Tactic.Exhaustion using (exhaustion₃)

module _ where
  open Data.Product

  anyTwo : Bit → Bit → Bit → Bit
  anyTwo x y z = x ∧ y ∨ y ∧ z ∨ x ∧ z

  fullAdder-ref : Bit → Bit → Bit → Bit × Bit
  fullAdder-ref x y c = (x ⊕ y ⊕ c , anyTwo x y c)

data Type : Set where
  :bit : Type

data Op : List Type → List Type → Set where
  :and :or :xor : Op (:bit ∷ :bit ∷ []) [ :bit ]
  :high :low : Op [] [ :bit ]
  :not : Op [ :bit ] [ :bit ]

schema : PolyQuiver _ _ _
schema = record
  { Type = Type
  ; _⇒_ = Op
  ; _≈_ = _≡_
  ; equiv = ≡.isEquivalence
  }

open Syntax schema hiding (Type; _△_)
module C = CartesianCategory ⇒CC

bit : Obj
bit = prim :bit

module _ where
  open Data.Product

  interpType : Type → Set
  interpType :bit = Bit

  interpMor
    : ∀ {As Bs}
    → Op As Bs
    → toCCObj →CC′ (List.map interpType As)
    → toCCObj →CC′ (List.map interpType Bs)
    -- flatten₀ →CC′ (mapObj interpType A) → flatten₀ →CC′ (mapObj interpType B)
  interpMor :and (x , y) = x ∧ y
  interpMor :or (x , y) = x ∨ y
  interpMor :xor (x , y) = x ⊕ y
  interpMor :high x = one
  interpMor :low x = zero
  interpMor :not x = Bit.not x

  toFunction″ : PQMorphism schema (ccToPolyQuiver →CC′)
  toFunction″ = record
    { map₀ = interpType
    ; map₁ = λ f → wrap (interpMor f)
    ; map₁-resp-≈ = λ f≡g x → ≡.cong₂ interpMor f≡g refl
    }

  toFunction′ : Functor ⇒Cat (Syntax.⇒Cat (ccToPolyQuiver →CC′))
  toFunction′ = mapSyntax toFunction″

  toFunction : Functor ⇒Cat (→Cat _)
  toFunction = flatten →CC′ ○ toFunction′

and or xor : bit ⊗ bit ⇒ bit
and = prim :and
or = prim :or
xor = prim :xor

high low : 𝟏 ⇒ bit
high = prim :high
low = prim :low

not : bit ⇒ bit
not = prim :not

module _ where
  open Gel ⇒CC
  open CartesianCategory ⇒CC using (_△_)
  open DoNotation

  halfAdder : bit ⊗ bit ⇒ bit ⊗ bit
  halfAdder = Λ xy ⇒ do
    let x = ! proj₁ xy
        y = ! proj₂ xy
    x+y ← xor $ x △ y
    c ← and $ x △ y
    x+y △ c

  fullAdder : bit ⊗ bit ⊗ bit ⇒ bit ⊗ bit
  fullAdder = Λ xyc ⇒ do
    let x = ! proj₁ xyc
        y = ! proj₁ (proj₂ xyc)
        c = ! proj₂ (proj₂ xyc)

    xy,c₀ ← halfAdder $ x △ y
    let xy = ! proj₁ xy,c₀
        c₀ = ! proj₂ xy,c₀

    xyc,c₁ ← halfAdder $ xy △ c
    let xyc = ! proj₁ xyc,c₁
        c₁ = ! proj₂ xyc,c₁

    co ← or $ c₀ △ c₁

    xyc △ co

module _ where
  open Data.Product
  open ≡.≡-Reasoning

  fullAdder-spec
    : ∀ x y z
    → Functor.map₁ toFunction fullAdder (x , y , z) ≡ fullAdder-ref x y z
  fullAdder-spec x y z =
    begin
      Functor.map₁ toFunction fullAdder (x , y , z)
    ≡⟨⟩
      ((x ⊕ y) ⊕ z , x ∧ y ∨ (x ⊕ y) ∧ z)
    ≡⟨ ≡.cong₂ _,_ refl
          (exhaustion₃ (λ x y z → x ∧ y ∨ (x ⊕ y) ∧ z ≡ x ∧ y ∨ y ∧ z ∨ x ∧ z) x y z) ⟩
      ((x ⊕ y) ⊕ z , x ∧ y ∨ y ∧ z ∨ x ∧ z)
    ≡⟨ ≡.cong₂ _,_ (⊕-assoc x y z) refl ⟩
      (x ⊕ y ⊕ z , x ∧ y ∨ y ∧ z ∨ x ∧ z)
    ≡⟨⟩
      fullAdder-ref x y z
    ∎
