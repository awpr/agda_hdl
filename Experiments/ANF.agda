module Experiments.ANF where

-- open import Agda.Primitive using (Lift)

open import Data.List using (List; []; _∷_; [_]; replicate; map)
open import Data.Fin using (Fin)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_∘_; id)
open import Level using (Lift)
open import Relation.Binary.Definitions using (_Respectsˡ_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong₂; _≗_)

open import Data.Bit
open import Instances
open import Experiments.FixedBinary using (Int; ext; _#_; _+_; _-_; _₀; _₁)

-- Level-polymorphic ⊤
--
-- Otherwise nullary ops would be accompanied by a 'lift ? tt' operand list.
record ⊤ω {l} : Set l where
  constructor ∅

-- Not Data.List.All literally just so we can use comma syntax.
all : ∀ {a p} {A : Set a} (P : A → Set p) → List A → Set p
all P [] = ⊤ω
all P (x ∷ []) = P x
all P (x ∷ xs) = P x × all P xs

all-map
  : ∀ {a b c} {A : Set a} {B : Set b} (f : A → B) (P : B → Set c) (xs : List A)
  → all (P ∘ f) xs ≡ all P (map f xs)
all-map f P [] = refl
all-map f P (x ∷ []) = refl
all-map f P (x ∷ x₁ ∷ xs) rewrite all-map f P (x₁ ∷ xs) = refl

all-equiv
  : ∀ {a p} {A : Set a} {P Q : A → Set p} (xs : List A)
  → P ≗ Q → all P xs ≡ all Q xs
all-equiv [] P≗Q = refl
all-equiv (x ∷ []) P≗Q = P≗Q x
all-equiv (x ∷ xs@(_ ∷ _)) P≗Q = cong₂ _×_ (P≗Q x) (all-equiv xs P≗Q)

respˡ : ∀ {a p} {A : Set a} → all {a} {p} {A} Respectsˡ _≗_
respˡ {y = xs} P≗Q Pxs = ≡.subst id (all-equiv xs P≗Q) Pxs

module _
  {Type : Set}
  (_⇒_ : List Type → List Type → Set)
  (⟦_⟧ : Type → Set) where
  infix 3 _∙_
  record Op (Bs : List Type) : Set where
    constructor _∙_
    field
      {As} : List Type
      op : As ⇒ Bs
      args : all ⟦_⟧ As

  data ANF (A : Set) : Set where
    return : A → ANF A
    bind
      : ∀ {As}
      → (op : Op As)
      → (q : all ⟦_⟧ As → ANF A)
      → ANF A

  Alg : Set
  Alg = ∀ {As} → Op As → all ⟦_⟧ As

mapOp
  : ∀ {T₁ T₂} {Rs : List T₁} {V : T₂ → Set}
  → {G : List T₁ → List T₁ → Set}
  → {K : List T₂ → List T₂ → Set}
  → (tf : T₁ → T₂)
  → (∀ {As Bs} → G As Bs → K (map tf As) (map tf Bs))
  → Op G (V ∘ tf) Rs → Op K V (map tf Rs)
mapOp {V = V} tf f (_∙_ {As} op args) rewrite all-map tf V As = f op ∙ args

module _
  {Type : Set}
  {_⇒_ : List Type → List Type → Set}
  {⟦_⟧ : Type → Set} where

  private ⟦⋆_⟧ : List Type → Set
  ⟦⋆ Ts ⟧ = all ⟦_⟧ Ts

  foldANF : ∀ {A} → Alg _⇒_ ⟦_⟧ → ANF _⇒_ ⟦_⟧ A → A
  foldANF alg (return x) = x
  foldANF alg (bind op q) = foldANF alg (q (alg op))

  subst
    : ∀ {A B}
    → ANF _⇒_ ⟦_⟧ A
    → (A → ANF _⇒_ ⟦_⟧ B)
    → ANF _⇒_ ⟦_⟧ B
  subst (return rs) q = q rs
  subst (bind op q₁) q = bind op (λ rs → subst (q₁ rs) q)

  _>>=_ : ∀ {As B} → Op _⇒_ ⟦_⟧ As → (⟦⋆ As ⟧ → ANF _⇒_ ⟦_⟧ B) → ANF _⇒_ ⟦_⟧ B
  _>>=_ = bind

module VerilogEx where
  data Logic : Set where
    zero one X Z : Logic

  data Type : Set where
    bit : Type
    int : Type
    logic : Type
    _⟨_⟩ : Type → ℕ → Type

  ⟦_⟧ : Type → Set
  ⟦ bit ⟧ = Bit
  ⟦ int ⟧ = Int 32
  ⟦ logic ⟧ = Logic
  ⟦ t ⟨ n ⟩ ⟧ = Vec ⟦ t ⟧ n

  -- Enable ops to be polymorphic over scalars and vectors while
  -- distinguishing 1-element vectors from scalars.
  data ℕ? : Set where
    scalar : ℕ?
    vector : ℕ → ℕ?

  Vec? : Set → ℕ? → Set
  Vec? A scalar = A
  Vec? A (vector n) = Vec A n

  _⟪_⟫ : Type → ℕ? → Type
  t ⟪ scalar ⟫ = t
  t ⟪ vector n ⟫ = t ⟨ n ⟩

  data Prim : List Type → List Type → Set where
    and or xor nand : ∀ {n} → Prim (bit ⟪ n ⟫ ∷ bit ⟪ n ⟫ ∷ []) [ bit ⟪ n ⟫ ]
    ¬ : ∀ {n} → Prim [ bit ⟪ n ⟫ ] [ bit ⟪ n ⟫ ]
    high low : ∀ {n} → Prim [] [ bit ⟪ n ⟫ ]
    append : ∀ {T n m} → Prim (T ⟨ n ⟩ ∷ T ⟨ m ⟩ ∷ []) [ T ⟨ n ℕ.+ m ⟩ ]
    index : ∀ {T n} (i : Fin n) → Prim [ T ⟨ n ⟩ ] [ T ]
    lit : ∀ {T} → ⟦ T ⟧ → Prim [] [ T ]
    add sub : ∀ {n} → Prim (int ⟪ n ⟫ ∷ int ⟪ n ⟫ ∷ []) [ int ⟪ n ⟫ ]
    vec : ∀ {T} n → Prim (replicate n T) [ T ⟨ n ⟩ ]
    -- slice : ∀ {n} i j → Prim [ bit ⟨ n ⟩ ] [ bit ⟨ m ⟩ ]

  pattern _′[_] v i = index i ∙ v
  pattern _′+_ x y = add ∙ x , y
  pattern _′-_ x y = sub ∙ x , y

  replicate? : ∀ {n A} → ⟦ A ⟧ → ⟦ A ⟪ n ⟫ ⟧
  replicate? {scalar} x = x
  replicate? {vector _} x = Data.Vec.replicate x

  map? : ∀ {n} {A B : Type} → (⟦ A ⟧ → ⟦ B ⟧) → ⟦ A ⟪ n ⟫ ⟧ → ⟦ B ⟪ n ⟫ ⟧
  map? {scalar} f = f
  map? {vector _} f = Data.Vec.map f

  zipWith? : ∀ {n} {A B C : Type} → (⟦ A ⟧ → ⟦ B ⟧ → ⟦ C ⟧) → ⟦ A ⟪ n ⟫ ⟧ → ⟦ B ⟪ n ⟫ ⟧ → ⟦ C ⟪ n ⟫ ⟧
  zipWith? {scalar} f x y = f x y
  zipWith? {vector _} f x y = Data.Vec.zipWith f x y

  buildVec : ∀ {T} n → all ⟦_⟧ (replicate n T) → Vec ⟦ T ⟧ n
  buildVec 0 ∅ = []
  buildVec 1 x = x ∷ []
  buildVec (suc (suc n)) (x , xs) = x ∷ buildVec (suc n) xs

  interpPrim : Alg Prim ⟦_⟧
  interpPrim (and ∙ fst , snd) = zipWith? _∧_ fst snd
  interpPrim (or ∙ fst , snd) = zipWith? _∨_ fst snd
  interpPrim (xor ∙ fst , snd) = zipWith? _⊕_ fst snd
  interpPrim (nand ∙ fst , snd) = zipWith? _↑_ fst snd
  interpPrim (¬ ∙ args) = map? not args
  interpPrim (high ∙ ∅) = replicate? 1
  interpPrim (low ∙ args) = replicate? 0
  interpPrim (append ∙ fst , snd) = fst Data.Vec.++ snd
  interpPrim (v ′[ i ]) = Data.Vec.lookup v i
  interpPrim (lit x ∙ ∅) = x
  interpPrim (x ′+ y) = zipWith? _+_ x y
  interpPrim (x ′- y) = zipWith? _-_ x y
  interpPrim (vec n ∙ args) = buildVec n args

  example : ∀ {⟦_⟧} → ANF Prim ⟦_⟧ ⟦ int ⟨ 3 ⟩ ⟧
  example = do
    x ← lit {int} (ext (1 # [] ₁)) ∙ ∅
    y ← lit {int} (ext (1 # [] ₁)) ∙ ∅
    z ← add ∙ x , y
    zs ← vec 3 ∙ z , z , z
    return zs

open VerilogEx
