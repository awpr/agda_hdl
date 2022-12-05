module Experiments.Monad where

open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Function using (const; id; _∘_; _∘′_; _$_; λ-; _⟨_⟩_)
open import Function.Equality as Π using (_⟶_; _⟨$⟩_; cong; _⇨_; ≡-setoid)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as Trivial
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≗_; _→-setoid_; module ≡-Reasoning)
import Relation.Binary.PropositionalEquality.Properties as ≡

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Category.Setoids using (curry; uncurry)

-- Trying out monads parameterized over setoids.  I expect we'll need
-- to use the monad laws to write proofs, and formulating those monad
-- laws in terms of ≡ will end up forcing me to postulate
-- extensionality to prove them for certain monads, so this
-- formulation should hopefully allow them to be written in terms of
-- other relations, e.g. pointwise equality for a state monad.

private
  variable
    a b c ℓ : Level

-- 'cong' over the first argument of a binary equality-preserving function
congˡ
  : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Setoid a ℓ₁} {B : Setoid b ℓ₂} {C : Setoid c ℓ₃}
  → {x₁ x₂ : Setoid.Carrier A}
  → {y : Setoid.Carrier B}
  → (f : A ⟶ B ⇨ C)
  → x₁ ⟨ Setoid._≈_ A ⟩ x₂
  → f ⟨$⟩ x₁ ⟨$⟩ y ⟨ Setoid._≈_ C ⟩ f ⟨$⟩ x₂ ⟨$⟩ y
congˡ {B = B} f x₁≈x₂ = cong f x₁≈x₂ (Setoid.refl B)

congʳ
  : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Setoid a ℓ₁} {B : Setoid b ℓ₂} {C : Setoid c ℓ₃}
  → {x : Setoid.Carrier A}
  → {y₁ y₂ : Setoid.Carrier B}
  → (f : A ⟶ B ⇨ C)
  → y₁ ⟨ Setoid._≈_ B ⟩ y₂
  → f ⟨$⟩ x ⟨$⟩ y₁ ⟨ Setoid._≈_ C ⟩ f ⟨$⟩ x ⟨$⟩ y₂
congʳ {A = A} f y₁≈y₂ = cong f (Setoid.refl A) y₁≈y₂

-- _⟨_⟩_ (infix binary application) for equality-preserving functions
infixl 1 _⟨_$⟩_
_⟨_$⟩_
  : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Setoid a ℓ₁} {B : Setoid b ℓ₂} {C : Setoid c ℓ₃}
  → Setoid.Carrier A → (A ⟶ B ⇨ C) → Setoid.Carrier B → Setoid.Carrier C
x ⟨ f $⟩ y = f ⟨$⟩ x ⟨$⟩ y

module Core where
  Map : (Set a → Setoid b ℓ) → Set (suc a ⊔ b ⊔ ℓ)
  Map F = ∀ {A B} → (f : A → B) → F A ⟶ F B

  Pure : (Set a → Setoid b ℓ) → Set (suc a ⊔ b)
  Pure F = ∀ {A} → A → Setoid.Carrier (F A)

  Ap : (Set a → Setoid b ℓ) → Set (suc a ⊔ b ⊔ ℓ)
  Ap F = ∀ {A B} → F (A → B) ⟶ F A ⇨ F B

  _′⇨_ : Set a → Setoid b ℓ → Setoid (a ⊔ b) (a ⊔ ℓ)
  A ′⇨ B = ≡-setoid A (Trivial.indexedSetoid B)

  Bind : (Set a → Setoid b ℓ) → Set (suc a ⊔ b ⊔ ℓ)
  Bind M = ∀ {A B} → M A ⟶ (A ′⇨ M B) ⇨ M B

module Definitions where
  open Core

  MapId : (F : Set a → Setoid b ℓ) → Map F → Set (suc a ⊔ b ⊔ ℓ)
  MapId F map = ∀ {A} → let open Setoid (F A) in (x : Carrier) → map id ⟨$⟩ x ≈ x

  MapCompose : (F : Set a → Setoid b ℓ) → Map F → Set (suc a ⊔ b ⊔ ℓ)
  MapCompose F map =
    ∀ {A B C} → let open Setoid (F C) in (f : B → C) (g : A → B) (x : Setoid.Carrier (F A))
    → map (f ∘ g) ⟨$⟩ x ≈ map f ⟨$⟩ (map g ⟨$⟩ x)

  PureId : (F : Set a → Setoid b ℓ) → Pure F → Ap F → Set (suc a ⊔ b ⊔ ℓ)
  PureId F pure ap = ∀ {A} → let open Setoid (F A) in (x : Carrier) → (ap ⟨$⟩ pure id ⟨$⟩ x) ≈ x

  Pure∘ : (F : Set a → Setoid b ℓ) → Pure F → Ap F → Set (suc a ⊔ b ⊔ ℓ)
  Pure∘ F pure ap =
    ∀ {A B C}
    → let open Setoid (F C) in
      (u : Setoid.Carrier (F (B → C)))
    → (v : Setoid.Carrier (F (A → B)))
    → (w : Setoid.Carrier (F A))
    → ap ⟨$⟩ (ap ⟨$⟩ (ap ⟨$⟩ pure _∘′_ ⟨$⟩ u) ⟨$⟩ v) ⟨$⟩ w ≈ ap ⟨$⟩ u ⟨$⟩ (ap ⟨$⟩ v ⟨$⟩ w)

  Homomorphic : (F : Set a → Setoid b ℓ) → Pure F → Ap F → Set (suc a ⊔ ℓ)
  Homomorphic F pure ap =
    ∀ {A B} (f : A → B) (x : A)
    → let open Setoid (F B) in (ap ⟨$⟩ pure f ⟨$⟩ pure x) ≈ pure (f x)

  Interchange : (F : Set a → Setoid b ℓ) → Pure F → Ap F → Set (suc a ⊔ b ⊔ ℓ)
  Interchange F pure ap =
    ∀ {A B} (u : Setoid.Carrier (F (A → B))) (y : A)
    → let open Setoid (F B) in (ap ⟨$⟩ u ⟨$⟩ pure y) ≈ ap ⟨$⟩ (pure (_$ y)) ⟨$⟩ u

  LeftIdentity : (M : Set a → Setoid b ℓ) → Pure M → Bind M → Set (suc a ⊔ b ⊔ ℓ)
  LeftIdentity M pure bind =
    ∀ {A B} → let open Setoid (M B) in (x : A) (k : A → Carrier) → bind ⟨$⟩ pure x ⟨$⟩ k ≈ k x

  RightIdentity : (M : Set a → Setoid b ℓ) → Pure M → Bind M → Set (suc a ⊔ b ⊔ ℓ)
  RightIdentity M pure bind =
    ∀ {A} → let open Setoid (M A) in (x : Carrier) → bind ⟨$⟩ x ⟨$⟩ pure ≈ x

  Associative  : (M : Set a → Setoid b ℓ) → Pure M → Bind M → Set (suc a ⊔ b ⊔ ℓ)
  Associative M pure bind =
    ∀ {A B C}
    → let open Setoid (M C) in
      (m : Setoid.Carrier (M A))
    → (k : A → Setoid.Carrier (M B))
    → (h : B → Setoid.Carrier (M C))
    → (bind ⟨$⟩ m ⟨$⟩ λ x → bind ⟨$⟩ k x ⟨$⟩ h) ≈ bind ⟨$⟩ (bind ⟨$⟩ m ⟨$⟩ k) ⟨$⟩ h

module Structures where
  open Core
  open Definitions

  record IsFunctor (F : Set a → Setoid b ℓ) (map : Map F) : Set (suc a ⊔ b ⊔ ℓ) where
    field
      map-id : MapId F map
      map-compose : MapCompose F map

  record IsApplicative
      (F : Set a → Setoid b ℓ)
      (pure : Pure F)
      (ap : Ap F)
      : Set (suc a ⊔ b ⊔ ℓ) where
    field
      pure-id : PureId F pure ap
      pure-∘ : Pure∘ F pure ap
      homomorphic : Homomorphic F pure ap
      interchange : Interchange F pure ap

  record IsMonad
      (M : Set a → Setoid b ℓ)
      (pure : Pure M)
      (bind : Bind M)
      : Set (suc a ⊔ b ⊔ ℓ) where
    field
      left-identity : LeftIdentity M pure bind
      right-identity : RightIdentity M pure bind
      associative : Associative M pure bind

module Bundles where
  open Core
  open Definitions
  open Structures

  record Functor a b ℓ : Set (suc (a ⊔ b ⊔ ℓ)) where
    field
      F : Set a → Setoid b ℓ
      map : Map F

      isFunctor : IsFunctor F map

    _<$>_ = map

    _<$_ : ∀ {A B : Set a} → B → F A ⟶ F B
    _<$_ = map ∘ const

  record Applicative a b ℓ : Set (suc (a ⊔ b ⊔ ℓ)) where
    field
      F : Set a → Setoid b ℓ
      pure : Pure F
      ap : Ap F

      isApplicative : IsApplicative F pure ap

    open IsApplicative isApplicative public

    infixl 20 _⊛_
    _⊛_ : ∀ {A B} → Setoid.Carrier (F (A → B)) → Setoid.Carrier (F A) → Setoid.Carrier (F B)
    f ⊛ x = ap ⟨$⟩ f ⟨$⟩ x

    map : Map F
    map f = record
      { _⟨$⟩_ = λ x → pure f ⊛ x
      ; cong = λ {i} {j} i≈j →
          let open SetoidReasoning (F _) in
          begin
            pure f ⊛ i
          ≡⟨⟩
            ap ⟨$⟩ pure f ⟨$⟩ i
          ≈⟨ cong ap (Setoid.refl (F _)) i≈j ⟩
            ap ⟨$⟩ pure f ⟨$⟩ j
          ≡⟨⟩
            pure f ⊛ j
          ∎
      }

    isFunctor : IsFunctor F map
    isFunctor = record
      { map-id = λ x → pure-id x
      ; map-compose = λ f g x →
          let open SetoidReasoning (F _) in
          begin
            map (f ∘ g) ⟨$⟩ x
          ≡⟨⟩
            pure (f ∘ g) ⊛ x
          ≈˘⟨ cong ap (homomorphic (f ∘′_) g) (Setoid.refl (F _)) ⟩
            (pure (f ∘′_) ⊛ pure g) ⊛ x
          ≈˘⟨ cong ap (cong ap (homomorphic _∘′_ f) (Setoid.refl (F _))) (Setoid.refl (F _)) ⟩
            (pure _∘′_ ⊛ pure f ⊛ pure g) ⊛ x
          ≈⟨ pure-∘ (pure f) (pure g) x ⟩
            pure f ⊛ (pure g ⊛ x)
          ≡⟨⟩
            map f ⟨$⟩ (map g ⟨$⟩ x)
          ∎
      }

    toFunctor : Functor a b ℓ
    toFunctor = record { F = F ; map = map ; isFunctor = isFunctor }

  record Monad a b ℓ : Set (suc (a ⊔ b ⊔ ℓ)) where
    field
      toSetoid : Set a → Setoid b ℓ
      pure : Pure toSetoid
      bind : Bind toSetoid

      isMonad : IsMonad toSetoid pure bind

    open IsMonad isMonad public

    Carrier : Set a → Set b
    Carrier = Setoid.Carrier ∘ toSetoid

    _⟪_⟫ : Set a → Set b
    _⟪_⟫ = Carrier

    return : ∀ {A : Set a} → A → Carrier A
    return x = pure x

    infixl 1 _>>=_
    _>>=_ : ∀ {A B : Set a} → Carrier A → (A → Carrier B) → Carrier B
    x >>= f = bind ⟨$⟩ x ⟨$⟩ f

    ap : Ap toSetoid
    ap {B = B} = curry ⟨$⟩ record
      { _⟨$⟩_ = λ (f , x) → bind ⟨$⟩ f ⟨$⟩ λ f′ → bind ⟨$⟩ x ⟨$⟩ λ x′ → pure (f′ x′)
      ; cong = λ { {f , x} {g , y} (f≗g , x≗y) → cong bind f≗g (λ f′ → cong bind x≗y λ x′ → Setoid.refl (toSetoid B)) }
      }

    pure-id : PureId toSetoid pure ap
    pure-id {A = A} x =
      begin
        ap ⟨$⟩ pure id ⟨$⟩ x
      ≡⟨⟩
        (pure id >>= λ id′ → x >>= λ x′ → pure (id′ x′))
      ≈⟨ left-identity id (λ id′ → x >>= (λ x′ → pure (id′ x′))) ⟩
        (x >>= λ x′ → pure (id x′))
      ≈⟨ cong bind (Setoid.refl (toSetoid A)) (λ _ → Setoid.refl (toSetoid A)) ⟩
        (x >>= pure)
      ≈⟨ right-identity x ⟩
        x
      ∎
     where open SetoidReasoning (toSetoid A)

    pure-∘ : Pure∘ toSetoid pure ap
    pure-∘ {C = C} u v w =
      begin
        (pure _∘′_ ⟨ ap $⟩ u ⟨ ap $⟩ v ⟨ ap $⟩ w)

      ≡⟨⟩
        (((pure _∘′_ >>= λ ∘ → u >>= λ u′ → pure (∘ u′)) >>= λ ∘u → v >>= λ v′ → pure (∘u v′)) >>=
        λ uv → w >>= λ w′ → pure (uv w′))

      ≈⟨ congˡ bind (congˡ bind (left-identity _∘′_ _)) ⟩
        (((u >>= λ u′ → pure (_∘′_ u′)) >>= λ ∘u → v >>= λ v′ → pure (∘u v′)) >>=
        λ uv → w >>= λ w′ → pure (uv w′))

      ≈˘⟨ congˡ bind (associative u (λ u′ → pure (_∘′_ u′)) _) ⟩
        ((u >>= λ u′ → pure (_∘′_ u′) >>= λ ∘u → v >>= λ v′ → pure (∘u v′)) >>=
        λ uv → w >>= λ w′ → pure (uv w′))

      ≈⟨ congˡ bind (congʳ bind λ u′ → left-identity (_∘′_ u′) _) ⟩
        ((u >>= λ u′ → v >>= λ v′ → pure (u′ ∘ v′)) >>=
        λ uv → w >>= λ w′ → pure (uv w′))

      ≈˘⟨ associative u _ _ ⟩
        (u >>= λ u′ → (v >>= λ v′ → pure (u′ ∘ v′)) >>= λ uv → w >>= λ w′ → pure (uv w′))

      ≈˘⟨ congʳ bind (λ u′ → associative v _ _) ⟩
        (u >>= λ u′ → v >>= λ v′ → pure (u′ ∘ v′) >>= λ uv → w >>= λ w′ → pure (uv w′))

      ≈⟨ congʳ bind (λ u′ → congʳ bind (λ v′ → left-identity (u′ ∘ v′) _)) ⟩
        (u >>= λ u′ → v >>= λ v′ → w >>= λ w′ → pure (u′ (v′ w′)))

      ≈˘⟨ congʳ bind (λ u′ → congʳ bind (λ v′ → congʳ bind (λ w′ → left-identity (v′ w′) _))) ⟩
        (u >>= λ u′ → v >>= λ v′ → w >>= λ w′ → pure (v′ w′) >>= λ vw → pure (u′ vw))

      ≈⟨ congʳ bind (λ u′ → congʳ bind (λ v′ → associative w _ _)) ⟩
        (u >>= λ u′ → v >>= λ v′ → (w >>= λ w′ → pure (v′ w′)) >>= λ vw → pure (u′ vw))

      ≈⟨ congʳ bind (λ u′ → associative v _ _) ⟩
        (u >>= λ u′ → (v >>= λ v′ → w >>= λ w′ → pure (v′ w′)) >>= λ vw → pure (u′ vw))

      ≡⟨⟩
        (u ⟨ ap $⟩ (v ⟨ ap $⟩ w))
      ∎
     where open SetoidReasoning (toSetoid C)

    homomorphic : Homomorphic toSetoid pure ap
    homomorphic {B = B} f x =
      begin
        ap ⟨$⟩ pure f ⟨$⟩ pure x

      ≡⟨⟩
        (pure f >>= λ f′ → pure x >>= λ x′ → pure (f′ x′))

      ≈⟨ left-identity f _ ⟩
        (pure x >>= λ x′ → pure (f x′))

      ≈⟨ left-identity x _ ⟩
        pure (f x)
      ∎
     where open SetoidReasoning (toSetoid B)

    interchange : Interchange toSetoid pure ap
    interchange {B = B} u y =
      begin
        ap ⟨$⟩ u ⟨$⟩ pure y

      ≡⟨⟩
        (u >>= λ u′ → pure y >>= λ y′ → pure (u′ y′))

      ≈⟨ congʳ bind (λ u′ → left-identity y _) ⟩
        (u >>= λ u′ → pure (u′ y))

      ≈˘⟨ left-identity (_$ y) _ ⟩
        (pure (_$ y) >>= λ $y → u >>= λ u′ → pure ($y u′))

      ≡⟨⟩
        ap ⟨$⟩ pure (_$ y) ⟨$⟩ u
      ∎
     where open SetoidReasoning (toSetoid B)

    isApplicative : IsApplicative toSetoid pure ap
    isApplicative = record
      { pure-id = pure-id
      ; pure-∘ = pure-∘
      ; homomorphic = homomorphic
      ; interchange = interchange
      }

    toApplicative : Applicative a b ℓ
    toApplicative = record { F = toSetoid ; pure = pure ; ap = ap ; isApplicative = isApplicative }

    open Applicative toApplicative public using (map; isFunctor; toFunctor)

  open Monad public using (_⟪_⟫; Carrier; toSetoid)

module Reader {a r} (R : Set r) where
  open Core
  open Definitions
  open Structures
  open Bundles

  F : Set a → Setoid (r ⊔ a) (r ⊔ a)
  F A = R →-setoid A

  map : Map F
  map f = record
    { _⟨$⟩_ = λ g → f ∘ g
    ; cong = λ i≈j r → ≡.cong f (i≈j r)
    }

  map-id : MapId F map
  map-id R⇒A R = refl

  map-compose : MapCompose F map
  map-compose f g FA x = refl

  isFunctor : IsFunctor F map
  isFunctor = record
    { map-id = map-id
    ; map-compose = map-compose
    }

  ReaderFunctor : Functor a (r ⊔ a) (r ⊔ a)
  ReaderFunctor = record { F = F ; map = map ; isFunctor = isFunctor }

  pure : Pure F
  pure x r = x

  ap : Ap F
  ap = curry ⟨$⟩ record
    { _⟨$⟩_ = λ (f , x) r → f r (x r)
    ; cong = λ { {f , x} {g , y} (f≗g , x≗y) r → ≡.cong₂ id (f≗g r) (x≗y r) }
    }

  pure-id : PureId F pure ap
  pure-id x r = refl

  pure-∘ : Pure∘ F pure ap
  pure-∘ u v w r = refl

  homomorphic : Homomorphic F pure ap
  homomorphic f x r = refl

  interchange : Interchange F pure ap
  interchange u y r = refl

  isApplicative : IsApplicative F pure ap
  isApplicative = record
    { pure-id = pure-id
    ; pure-∘ = pure-∘
    ; homomorphic = homomorphic
    ; interchange = interchange
    }

  ReaderAp : Applicative a (r ⊔ a) (r ⊔ a)
  ReaderAp = record { F = F ; pure = pure ; ap = ap ; isApplicative = isApplicative }

  bind : Bind F
  bind = curry ⟨$⟩ record
    { _⟨$⟩_ = λ { (x , f) r → f (x r) r }
    ; cong = λ { {x₁ , f₁} {x₂ , f₂} (x₁≈x₂ , f₁≈f₂) r →
        let open ≡-Reasoning in
        begin
          f₁ (x₁ r) r
        ≡⟨ ≡.cong₂ f₁ (x₁≈x₂ r) refl ⟩
          f₁ (x₂ r) r
        ≡⟨ f₁≈f₂ (x₂ r) r ⟩
          f₂ (x₂ r) r
        ∎ }
    }

  left-identity : LeftIdentity F pure bind
  left-identity x k r = refl

  right-identity : RightIdentity F pure bind
  right-identity x r = refl

  associative : Associative F pure bind
  associative m k h r = refl

  isMonad : IsMonad F pure bind
  isMonad = record
    { left-identity = left-identity
    ; right-identity = right-identity
    ; associative = associative
    }

  Reader : Monad a (r ⊔ a) (r ⊔ a)
  Reader = record { toSetoid = F ; pure = pure ; bind = bind ; isMonad = isMonad }

module Vec {a} where
  open import Data.Nat
  open import Data.Vec as Vec hiding (map; _>>=_)
  open import Data.Vec.Properties hiding (map-id)

  open Core
  open Definitions
  open Structures
  open Bundles

  variable
    n : ℕ

  F : ℕ → Set a → Setoid a a
  F n A = ≡.setoid (Vec A n)

  map : Map (F n)
  map f = record { _⟨$⟩_ = Vec.map f ; cong = ≡.cong₂ Vec.map refl }

  map-id : MapId (F n) map
  map-id [] = refl
  map-id (x ∷ xs) = ≡.cong (x ∷_) (map-id xs)

  map-compose : MapCompose (F n) map
  map-compose f g [] = refl
  map-compose f g (x ∷ xs) = ≡.cong (f (g x) ∷_) (map-compose f g xs)

  isFunctor : IsFunctor (F n) map
  isFunctor = record { map-id = map-id ; map-compose = map-compose }

  VectorFunctor : ℕ → Functor a a a
  VectorFunctor n = record { F = F n; map = map ; isFunctor = isFunctor }

  pure : Pure (F n)
  pure = Vec.replicate

  ap : Ap (F n)
  ap = ≡.→-to-⟶ λ vf → ≡.→-to-⟶ (vf ⊛_)

  open ≡-Reasoning

  pure-id : PureId (F n) pure ap
  pure-id xs =
    begin
      pure id ⊛ xs
    ≡˘⟨ map-is-⊛ id xs ⟩
      Vec.map id xs
    ≡⟨ map-id xs ⟩
      xs
    ∎

  pure-∘ : Pure∘ (F n) pure ap
  pure-∘ [] [] [] = refl
  pure-∘ (f ∷ fs) (x ∷ xs) (y ∷ ys) = ≡.cong (f (x y) ∷_) (pure-∘ fs xs ys)

  homomorphic : Homomorphic (F n) pure ap
  homomorphic f x =
    begin
      pure f ⊛ pure x
    ≡⟨ ⊛-is-zipWith (replicate f) (replicate x) ⟩
      zipWith _$_ (pure f) (pure x)
    ≡⟨ zipWith-replicate _$_ f x ⟩
      pure (f x)
    ∎

  interchange : Interchange (F n) pure ap
  interchange u y =
    begin
      u ⊛ pure y
    ≡⟨ ⊛-is-zipWith u (replicate y) ⟩
      zipWith _$_ u (pure y)
    ≡⟨ zipWith-replicate₂ _$_ u y ⟩
      Vec.map (_$ y) u
    ≡⟨⟩
      Vec.map (_$_ (_$ y)) u
    ≡˘⟨ zipWith-replicate₁ _$_ (_$ y) u ⟩
      zipWith _$_ (pure (_$ y)) u
    ≡˘⟨ ⊛-is-zipWith (pure (_$ y)) u ⟩
      pure (_$ y) ⊛ u
    ∎

  isApplicative : IsApplicative (F n) pure ap
  isApplicative = record
    { pure-id = pure-id
    ; pure-∘ = pure-∘
    ; homomorphic = homomorphic
    ; interchange = interchange
    }

  VectorAp : ℕ → Applicative a a a
  VectorAp n = record { F = F n ; pure = pure ; ap = ap ; isApplicative = isApplicative }

  _>>=_ : ∀ {A : Set a} {B : Set b} → Vec A n → (A → Vec B n) → Vec B n
  [] >>= f = []
  (x ∷ xs) >>= f = head (f x) ∷ (xs >>= (tail ∘ f))

  >>=-cong : ∀ {A : Set a} {B : Set b} {f g : A → Vec B n}  → f ≗ g → _>>= f ≗ _>>= g
  >>=-cong f≗g [] = refl
  >>=-cong f≗g (x ∷ xs) = ≡.cong₂ _∷_ (≡.cong head (f≗g x)) (>>=-cong (≡.cong tail ∘ f≗g) xs)

  bind : Bind (F n)
  bind = curry ⟨$⟩ record
    { _⟨$⟩_ = λ (vx , f) → vx >>= f
    ; cong = λ { (refl , f≗g) → >>=-cong f≗g _ }
    }

  left-identity : LeftIdentity (F n) pure bind
  left-identity {zero} x k with [] ← k x = refl
  left-identity {ℕ.suc n} x k
    rewrite left-identity x (tail ∘ k)
    with (y ∷ ys) ← k x
    = refl

  right-identity : RightIdentity (F n) pure bind
  right-identity [] = refl
  right-identity (x ∷ xs) = ≡.cong₂ _∷_ refl (right-identity xs)

  >>=-tail : ∀ {A : Set a} {B : Set b} (f : A → Vec B (ℕ.suc n)) (xs : Vec A (ℕ.suc n)) → tail (xs >>= f) ≡ (tail xs) >>= (tail ∘ f)
  >>=-tail f (x ∷ xs) = refl

  >>=-head : ∀ {A : Set a} {B : Set b} (f : A → Vec B (ℕ.suc n)) (xs : Vec A (ℕ.suc n)) → head (xs >>= f) ≡ head (f (head xs))
  >>=-head f (x ∷ xs) = refl

  associative : Associative (F n) pure bind
  associative [] k h = refl
  associative (x ∷ xs) k h = ≡.cong₂ _∷_ (>>=-head h (k x)) $
    begin
      xs >>= (λ x₁ → tail (k x₁ >>= h))

    ≡⟨ (>>=-cong (λ x → >>=-tail h (k x)) xs) ⟩
      xs >>= (λ x₁ → (tail ∘ k) x₁ >>= (tail ∘ h))

    ≡⟨ associative xs (tail ∘ k) (tail ∘ h) ⟩
      (xs >>= (tail ∘ k)) >>= (tail ∘ h)
    ∎

  isMonad : IsMonad (F n) pure bind
  isMonad = record
    { left-identity = left-identity
    ; right-identity = right-identity
    ; associative = associative
    }

  Vector : ℕ → Monad a a a
  Vector n = record { toSetoid = F n ; pure = pure ; bind = bind ; isMonad = isMonad }

module Identity where
  open Bundles

  Identity : Monad a a a
  Identity = record
    { toSetoid = ≡.setoid
    ; pure = λ x → x
    ; bind = ≡.→-to-⟶ (λ x → record { _⟨$⟩_ = _$ x ; cong = λ f≗g → f≗g x })
    ; isMonad = record
        { left-identity = λ x k → refl
        ; right-identity = λ x → refl
        ; associative = λ m k h → refl
        }
    }
