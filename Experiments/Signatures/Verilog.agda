module Experiments.Signatures.Verilog where

open import Data.List as List using (List; []; _∷_; [_])
import Data.List.Properties as List
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Product
open import Data.Vec using (Vec; []; _∷_)
import Function
open import Relation.Binary.PropositionalEquality.Extras as ≡ using
  ( _≡_; _≗_; refl
  ; cong; subst₂
  )
import Relation.Binary.PropositionalEquality.Properties.Extras as ≡

open import Data.Bit as Bit using (Bit; zero; one; _⊕_; _∧_; _∨_)
open import Data.Bit.Properties using (⊕-assoc)
open import Data.Finite using ()

open import Categories.Cartesian using (CartesianCategory)
open import Categories.Category.Types using (→CC′; →Cat)
open import Categories.Functor using (Functor; _○_)
open import Categories.PolyQuiver using
  ( PolyQuiver; toCCObj
  ; PQMorphism; _∘M_
  ; ccToPolyQuiver; WrappedCC; wrap; Wrapped≈
  )
import Categories.Syntax.Cartesian as Syntax
open import Categories.Syntax.Cartesian.Functors using
  ( mapSyntax; flatten; flatten₀ ; map∘map₁≗map₁
  ; map₀-resp-≗; flatten₁-resp-≈; map₁-pointwise
  )
open Categories.Functor.FunctorOperators using (_₁_)
import Categories.Gel.Cartesian as Gel

open import Experiments.Signatures.Unityped as Unityped using (fullAdder-ref; anyTwo)

module _ where
  open Data.Product

  adder-ref : ∀ {n} → Vec Bit n → Vec Bit n → Bit → Vec Bit n × Bit
  adder-ref [] [] c = [] , c
  adder-ref (x ∷ xs) (y ∷ ys) c =
    let (xy , c₀) = fullAdder-ref x y c
        (xys , c₁) = adder-ref xs ys c₀
    in  xy ∷ xys , c₁

data Type : Set where
  :bit : Type
  :bit⟨_⟩ : ℕ → Type

data Op : List Type → List Type → Set where
  :cons : ∀ {n} → Op (:bit ∷ :bit⟨ n ⟩ ∷ []) [ :bit⟨ suc n ⟩ ]
  :uncons : ∀ {n} → Op [ :bit⟨ suc n ⟩ ] (:bit ∷ :bit⟨ n ⟩ ∷ [])
  :nil : Op [] [ :bit⟨ 0 ⟩ ]

  :and :or :xor : Op (:bit ∷ :bit ∷ []) [ :bit ]
  :not : Op [ :bit ] [ :bit ]
  :high :low : Op [] [ :bit ]

schema : PolyQuiver _ _ _
schema = record
  { Type = Type
  ; _⇒_ = Op
  ; _≈_ = _≡_
  ; equiv = ≡.isEquivalence
  }

open Syntax schema hiding (Type; _△_)

bit : Obj
bit = prim :bit

bit⟨_⟩ : ℕ → Obj
bit⟨ n ⟩ = prim :bit⟨ n ⟩

private module Uni where
  open import Experiments.Signatures.Unityped public
  open Syntax Experiments.Signatures.Unityped.schema public hiding (Type)

module _ where
  mapType : Uni.Type → Type
  mapType Uni.:bit = :bit

  mapMor
    : ∀ {As Bs}
    → Uni.Op As Bs
    → Op (List.map mapType As) (List.map mapType Bs)
  mapMor Uni.:and = :and
  mapMor Uni.:or = :or
  mapMor Uni.:xor = :xor
  mapMor Uni.:high = :high
  mapMor Uni.:low = :low
  mapMor Uni.:not = :not

  fromUnityped′ : PQMorphism Uni.schema schema
  fromUnityped′ = record
    { map₀ = mapType
    ; map₁ = mapMor
    ; map₁-resp-≈ = cong mapMor
    }

  fromUnityped : Functor (Syntax.⇒Cat Uni.schema) ⇒Cat
  fromUnityped = mapSyntax fromUnityped′

module _ where
  open Data.Product

  interpType : Type → Set
  interpType :bit = Bit
  interpType :bit⟨ n ⟩ = Vec Bit n

  interpMor
    : ∀ {As Bs}
    → Op As Bs
    → toCCObj →CC′ (List.map interpType As)
    → toCCObj →CC′ (List.map interpType Bs)
    -- → flatten₀ →CC′ (mapObj interpType A) → flatten₀ →CC′ (mapObj interpType B)
  interpMor :cons (x , xs) = x ∷ xs
  interpMor :uncons (x ∷ xs) = x , xs
  interpMor :nil _ = []
  interpMor :and (x , y) = x ∧ y
  interpMor :or (x , y) = x ∨ y
  interpMor :xor (x , y) = x ⊕ y
  interpMor :not x = Bit.not x
  interpMor :high _ = one
  interpMor :low _ = zero

  toFunction″ : PQMorphism schema (ccToPolyQuiver →CC′)
  toFunction″ = record
    { map₀ = interpType
    ; map₁ = λ f → wrap (interpMor f)
    ; map₁-resp-≈ = λ f≡g x → ≡.cong (λ f′ → interpMor f′ x) f≡g
    }

  toFunction′ : Functor ⇒Cat (Syntax.⇒Cat (ccToPolyQuiver →CC′))
  toFunction′ = mapSyntax toFunction″

  toFunction : Functor ⇒Cat (→Cat _)
  toFunction = flatten →CC′ ○ toFunction′

  interpType-≗ : interpType Function.∘ mapType ≗ Uni.interpType
  interpType-≗ Uni.:bit = refl

  interpMor-≗
    : ∀ {As Bs} (f : Uni.Mor As Bs)
    → Wrapped≈ →CC′ _≗_
        (subst₂
          (WrappedCC →CC′)
          (List.map-cong interpType-≗ As)
          (List.map-cong interpType-≗ Bs)
          (PQMorphism.map₁ (toFunction″ ∘M fromUnityped′) f))
        (PQMorphism.map₁ Uni.toFunction″ f)
  interpMor-≗ Uni.:and  _ = refl
  interpMor-≗ Uni.:or   _ = refl
  interpMor-≗ Uni.:xor  _ = refl
  interpMor-≗ Uni.:high _ = refl
  interpMor-≗ Uni.:low  _ = refl
  interpMor-≗ Uni.:not  _ = refl

and or xor : bit ⊗ bit ⇒ bit
and = prim :and
or = prim :or
xor = prim :xor

uncons : ∀ {n} → bit⟨ suc n ⟩ ⇒ bit ⊗ bit⟨ n ⟩
uncons = prim :uncons

cons : ∀ {n} → bit ⊗ bit⟨ n ⟩ ⇒ bit⟨ suc n ⟩
cons = prim :cons

nil : 𝟏 ⇒ bit⟨ zero ⟩
nil = prim :nil

high low : 𝟏 ⇒ bit
high = prim :high
low = prim :low

fullAdder : bit ⊗ bit ⊗ bit ⇒ bit ⊗ bit
fullAdder = Functor.map₁ fromUnityped Uni.fullAdder

module _ where
  open Gel ⇒CC
  open DoNotation
  open CartesianCategory ⇒CC using (_△_)

  adder : ∀ {n} → bit⟨ n ⟩ ⊗ bit⟨ n ⟩ ⊗ bit ⇒ bit⟨ n ⟩ ⊗ bit
  adder {zero} = Λ xyc ⇒ (! nil) △ proj₂ (proj₂ xyc)
  adder {suc n} = Λ xyc ⇒ do
    let x = ! proj₁ xyc
        y = ! proj₁ (proj₂ xyc)
        c = proj₂ (proj₂ xyc)
        x₀ = proj₁ (uncons $ x)
        y₀ = proj₁ (uncons $ y)

    xy₀,c′ ← fullAdder $ x₀ △ y₀ △ c
    let c′ = proj₂ xy₀,c′
        xs = proj₂ (uncons $ x)
        ys = proj₂ (uncons $ y)

    xys,co ← adder $ xs △ ys △ c′
    let xy₀ = proj₁ xy₀,c′
        xys = proj₁ xys,co
        co = proj₂ xys,co

    (cons $ xy₀ △ xys) △ co

module _ where
  open Data.Product
  open ≡.≡-Reasoning

  open Categories.Functor.FunctorOperators

  fullAdder-spec
    : ∀ x y c
    → (toFunction ₁ fullAdder) (x , y , c) ≡ fullAdder-ref x y c
  fullAdder-spec x y c =
    let b = Uni.bit
        A = b ⊗ b ⊗ b
        B = b ⊗ b in
    begin
      (toFunction ₁ fullAdder) (x , y , c)

    ≡⟨⟩
      (flatten →CC′ ₁ mapSyntax toFunction″ ₁ mapSyntax fromUnityped′ ₁ Uni.fullAdder)
        (x , y , c)

    ≡⟨ cong
          (λ X → (flatten →CC′ ₁ X) (x , y , c))
          (map∘map₁≗map₁ toFunction″ fromUnityped′ Uni.fullAdder) ⟩
      (flatten →CC′ ₁ mapSyntax (toFunction″ ∘M fromUnityped′) ₁ Uni.fullAdder)
        (x , y , c)

    ≡⟨ flatten₁-resp-≈ →CC′
          (map₁-pointwise
            (toFunction″ ∘M fromUnityped′)
            Uni.toFunction″
            interpType-≗
            interpMor-≗
            (Uni.C.≈.refl {_} {_} {Uni.fullAdder})) (x , y , c) ⟩
      (flatten →CC′ ₁ mapSyntax Uni.toFunction″ ₁ Uni.fullAdder)
        (x , y , c)

    ≡⟨⟩
      (Uni.toFunction ₁ Uni.fullAdder)
        (x , y , c)

    ≡⟨ Uni.fullAdder-spec x y c ⟩
      fullAdder-ref x y c
    ∎

  adder-spec
    : ∀ {n} (x y : Vec Bit n) c
    → Functor.map₁ toFunction adder (x , y , c) ≡ adder-ref x y c
  adder-spec {zero} [] [] c = refl
  adder-spec {suc n} (x ∷ xs) (y ∷ ys) c =
    begin
      Functor.map₁ toFunction adder (x ∷ xs , y ∷ ys , c)

    ≡⟨⟩
      let (xy , c₀) = Functor.map₁ toFunction fullAdder (x , y , c)
          (xys , c₁) = Functor.map₁ toFunction adder (xs , ys , c₀)
      in  xy ∷ xys , c₁

    ≡⟨ ≡.cong
          (λ (xy , c₀) →
            let (xys , c₁) = Functor.map₁ toFunction adder (xs , ys , c₀)
            in  xy ∷ xys , c₁)
          (fullAdder-spec x y c) ⟩
      let (xy , c₀) = fullAdder-ref x y c
          (xys , c₁) = Functor.map₁ toFunction adder (xs , ys , c₀)
      in  xy ∷ xys , c₁

    ≡⟨ ≡.cong (λ (xys , c′) → (x ⊕ y ⊕ c) ∷ xys , c′) (adder-spec xs ys (anyTwo x y c)) ⟩
      let (xy , c₀) = fullAdder-ref x y c
          (xys , c₁) = adder-ref xs ys c₀
      in  xy ∷ xys , c₁

    ≡⟨⟩
      adder-ref (x ∷ xs) (y ∷ ys) c
    ∎
