module Experiments.Free where

open import Function using (_∘_; _$_; id)
open import Data.List using (List; []; _∷_; [_]; replicate; map)
open import Data.List.Properties using (map-id)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; []; _∷_)
open import Category.Monad using (RawMonad)
open import Relation.Binary.HeterogeneousEquality as ≅ using
  (_≅_; ≅-to-≡; ≡-to-≅; module ≅-Reasoning)
open import Relation.Binary.PropositionalEquality using
  ( _≡_; refl; cong; subst; sym; module ≡-Reasoning
  ; _≗_
  )

open import Experiments.ANF as ANF using (ANF; Op; Alg; all; _∙_; ∅)
open import Data.Bit
open import Data.Finite
open import Instances
open import Tactic.Exhaustion

module _
  {Type : Set}
  (_⇒_ : List Type → List Type → Set)
  (⟦_⟧ : Type → Set) where

  data Free : Set → Set₁ where
    prim : ∀ {Rs} → (op : Op _⇒_ ⟦_⟧ Rs) → Free (all ⟦_⟧ Rs)
    done : ∀ {A} → A → Free A
    bind : ∀ {A B} → (x : Free B) → (q : B → Free A) → Free A

module _
  {Type : Set}
  (G : List Type → List Type → Set) where

  record Open (As Bs : List Type) : Set₁ where
    constructor MkOpen
    field
      run : ∀ {V} → all V As → ANF G V (all V Bs)

module _
  {Type : Set}
  {_⇒_ : List Type → List Type → Set}
  {⟦_⟧ : Type → Set} where

  -- RawMonad is not level-polymorphic in stdlib 1.7.1 (but it is at
  -- GitHub master).  So, for now, the do-notation for Free has to
  -- come from standalone functions.
  module FreeDoNotation where
    _>>=_
      : ∀ {A B}
      → Free _⇒_ ⟦_⟧ A
      → (A → Free _⇒_ ⟦_⟧ B)
      → Free _⇒_ ⟦_⟧ B
    _>>=_ = bind

    _>>_
      : ∀ {A B}
      → Free _⇒_ ⟦_⟧ A → Free _⇒_ ⟦_⟧ B → Free _⇒_ ⟦_⟧ B
    x >> y = x >>= λ _ → y

    return : ∀ {A} → A → Free _⇒_ ⟦_⟧ A
    return = done

  foldFree
    : Alg _⇒_ ⟦_⟧
    → ∀ {A} → Free _⇒_ ⟦_⟧ A → A
  foldFree alg (prim op) = alg op
  foldFree alg (done x) = x
  foldFree alg (bind x q) = foldFree alg (q (foldFree alg x))

  foldMFree
    : ∀ {A} {M : Set → Set}
    → RawMonad M
    → (∀ {As} → Op _⇒_ ⟦_⟧ As → M (all ⟦_⟧ As))
    → Free _⇒_ ⟦_⟧ A
    → M A
  foldMFree rm alg (prim op) = alg op
  foldMFree rm alg (Free.done x) = RawMonad.pure rm x
  foldMFree rm alg (bind x q) = foldMFree rm alg x >>= foldMFree rm alg ∘ q
   where open RawMonad rm

  toANF : ∀ {Rs} → Free _⇒_ ⟦_⟧ Rs → ANF _⇒_ ⟦_⟧ Rs
  toANF (prim op) = ANF.bind op ANF.return
  toANF (done x) = ANF.return x
  toANF (bind x q) = ANF.subst (toANF x) (λ rs → toANF (q rs))

  fromANF : ∀ {Rs} → ANF _⇒_ ⟦_⟧ Rs → Free _⇒_ ⟦_⟧ Rs
  fromANF (ANF.return rs) = done rs
  fromANF (ANF.bind op q) = prim op >>= (fromANF ∘ q)
   where open FreeDoNotation

mapFree
  : ∀ {T₁ T₂ A} {V : T₂ → Set}
  → {G : List T₁ → List T₁ → Set}
  → {K : List T₂ → List T₂ → Set}
  → (tf : T₁ → T₂)
  → (∀ {Bs} → Op G (V ∘ tf) Bs → Op K V (Data.List.map tf Bs))
  → Free G (V ∘ tf) A → Free K V A
mapFree {V = V} tf f (prim {Rs} op) rewrite ANF.all-map tf V Rs = prim (f op)
mapFree tf f (done x) = done x
mapFree tf f (bind x q) = bind (mapFree tf f x) (mapFree tf f ∘ q)

-- mapFree, without changing the universe type.
mapFree′
  : ∀ {T A} {V : T → Set}
  → {G K : List T → List T → Set}
  → (∀ {Bs} → Op G V Bs → Op K V Bs)
  → Free G V A → Free K V A
mapFree′ {V = V} {K = K} f = mapFree id
  (λ {Bs} opg → subst (Op K V) (sym (map-id Bs)) (f opg))

_∘A_
  : ∀ {T₁ T₂} {V : T₂ → Set}
  → {G : List T₁ → List T₁ → Set}
  → {K : List T₂ → List T₂ → Set}
  → {tf : T₁ → T₂}
  → Alg K V → (∀ {Bs} → Op G (V ∘ tf) Bs → Op K V (map tf Bs)) → Alg G (V ∘ tf)
_∘A_ {V = V} {tf = tf} alg f {As} op rewrite ANF.all-map tf V As = alg (f op)

infix 4 _≛_
_≛_
  : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
  → (f g : ∀ {x : A} → P x → Q x)
  → Set _
_≛_ {A = A} {P = P} f g = ∀ {x : A} (Px : P x) → f Px ≡ g Px

-- Mapping and then folding is the same as folding by a composed algebra
fold-map
  : ∀ {T₁ T₂ A} {V : T₂ → Set}
  → {G : List T₁ → List T₁ → Set}
  → {K : List T₂ → List T₂ → Set}
  → (alg : Alg K V)
  → (tf : T₁ → T₂)
  → (f : ∀ {Bs} → Op G (V ∘ tf) Bs → Op K V (Data.List.map tf Bs))
  → foldFree alg {A} ∘ mapFree tf f ≗ foldFree (alg ∘A f)
fold-map {V = V} {G = G} alg tf f (prim {Rs} op)
  rewrite ANF.all-map tf V Rs
  = refl
fold-map alg tf f (done x) = refl
fold-map alg tf f (bind x q) =
  begin
    (foldFree alg ∘ mapFree tf f) (bind x q)

  ≡⟨⟩
    foldFree alg (bind (mapFree tf f x) (mapFree tf f ∘ q))

  ≡⟨⟩
    let x′ = foldFree alg (mapFree tf f x)
    in  foldFree alg (mapFree tf f (q x′))

  ≡⟨ cong (λ x′ → foldFree alg (mapFree tf f (q x′))) (fold-map alg tf f x) ⟩
    let x′ = foldFree (alg ∘A f) x
    in  foldFree alg (mapFree tf f (q x′))

  ≡⟨ fold-map alg tf f (q (foldFree (alg ∘A f) x)) ⟩
    let x′ = foldFree (alg ∘A f) x
    in  foldFree (alg ∘A f) (q x′)

  ≡⟨⟩
    foldFree (alg ∘A f) (bind x q)
  ∎
 where open ≡-Reasoning

castOp : ∀ {T} {V₁ V₂ : T → Set} {G As} → V₁ ≗ V₂ → Op G V₁ As → Op G V₂ As
castOp {T} V₁≗V₂ (_∙_ {Bs} op args) = op ∙ ANF.respˡ {y = Bs} V₁≗V₂ args

cast-cast
  : ∀ {T G V₁ V₂ Rs}
  → (V₁≗V₂ : V₁ ≗ V₂)
  → (V₂≗V₁ : V₂ ≗ V₁)
  → (op : Op {T} G V₁ Rs)
  → castOp V₂≗V₁ (castOp V₁≗V₂ op) ≡ op
cast-cast V₁≗V₂ V₂≗V₁ (_∙_ {As} op args) = ≅-to-≡ $
  begin
    castOp V₂≗V₁ (castOp V₁≗V₂ (_∙_ {As = As} op args))
  ≡⟨⟩
    (op ∙ subst id As₂≡As₁ (subst id As₁≡As₂ args))
  ≅⟨ ≅.cong (_∙_ {As = As} op) lemma ⟩
    (op ∙ args)
  ∎
 where
  open ≅-Reasoning

  As₂≡As₁ = ANF.all-equiv As V₂≗V₁
  As₁≡As₂ = ANF.all-equiv As V₁≗V₂

  lemma : subst id As₂≡As₁ (subst id As₁≡As₂ args) ≅ args
  lemma =
    begin
      subst id As₂≡As₁ (subst id As₁≡As₂ args)
    ≅⟨ ≅.≡-subst-removable id As₂≡As₁ (subst id As₁≡As₂ args) ⟩
      subst id As₁≡As₂ args
    ≅⟨ ≅.≡-subst-removable id As₁≡As₂ args ⟩
      args
    ∎

castAlg : ∀ {T V₁ V₂ G} → V₁ ≗ V₂ → Alg {T} G V₂ → Alg G V₁
castAlg V₁≗V₂ alg {As} op = subst id (ANF.all-equiv As (sym ∘ V₁≗V₂)) (alg (castOp V₁≗V₂ op))

castFree : ∀ {T A} {V₁ V₂ : T → Set} {G} → V₁ ≗ V₂ → Free G V₂ A → Free G V₁ A
castFree V₁≗V₂ (prim {Rs} op) =
  subst (Free _ _) (ANF.all-equiv Rs V₁≗V₂) (prim (castOp (sym ∘ V₁≗V₂) op))
castFree V₁≗V₂ (done x) = done x
castFree V₁≗V₂ (bind x q) = bind (castFree V₁≗V₂ x) (λ z → castFree V₁≗V₂ (q z))

fold-cast
  : ∀ {T V₁ V₂ G A}
  → (x : Free {T} G V₂ A)
  → (alg : Alg G V₂)
  → (V₁≗V₂ : V₁ ≗ V₂)
  → foldFree (castAlg V₁≗V₂ alg) (castFree V₁≗V₂ x) ≡ foldFree alg x
fold-cast {V₁ = V₁} {V₂} {G} (prim {Rs} op) alg V₁≗V₂ = ≅-to-≡ $
  begin
    foldFree (castAlg V₁≗V₂ alg) (castFree V₁≗V₂ (prim op))

  ≡⟨⟩
    foldFree
      (castAlg V₁≗V₂ alg)
      (subst (Free G V₁) Rs₁≡Rs₂ (prim (castOp V₂≗V₁ op)))

  ≅⟨ ≅.cong₂ {A = Set} {Free G V₁} {λ A _ → A}
       (λ A y → foldFree (castAlg V₁≗V₂ alg) y)
       (≡-to-≅ Rs₂≡Rs₁)
       (≅.≡-subst-removable (Free G V₁)
         (ANF.all-equiv Rs V₁≗V₂)
         (prim (castOp V₂≗V₁ op))) ⟩
    foldFree
      (castAlg V₁≗V₂ alg)
      (prim (castOp V₂≗V₁ op))

  ≡⟨⟩
    castAlg V₁≗V₂ alg (castOp V₂≗V₁ op)

  ≡⟨⟩
    subst id Rs₂≡Rs₁ (alg (castOp V₁≗V₂ (castOp V₂≗V₁ op)))

  ≅⟨ ≅.≡-subst-removable id Rs₂≡Rs₁ (alg (castOp V₁≗V₂ (castOp V₂≗V₁ op))) ⟩
    alg (castOp V₁≗V₂ (castOp V₂≗V₁ op))

  ≅⟨ ≅.cong alg (≡-to-≅ (cast-cast V₂≗V₁ V₁≗V₂ op)) ⟩
    alg op

  ≡⟨⟩
    foldFree alg (prim op)
  ∎
 where
  open ≅-Reasoning

  V₂≗V₁ = sym ∘ V₁≗V₂

  Rs₁≡Rs₂ : all V₁ Rs ≡ all V₂ Rs
  Rs₁≡Rs₂ = ANF.all-equiv Rs V₁≗V₂

  Rs₂≡Rs₁ : all V₂ Rs ≡ all V₁ Rs
  Rs₂≡Rs₁ = ANF.all-equiv Rs V₂≗V₁

fold-cast (done x) alg V₁≗V₂ = refl
fold-cast (bind x q) alg V₁≗V₂ rewrite fold-cast x alg V₁≗V₂ =
  fold-cast (q (foldFree alg x)) alg V₁≗V₂

fold-equiv′
  : ∀ {T} {G : List T → List T → Set} {V : T → Set}
  → (alg₁ alg₂ : Alg G V)
  → (∀ {As} → alg₁ {As} ≗ alg₂) → ∀ {A} → foldFree alg₁ {A} ≗ foldFree alg₂
fold-equiv′ alg₁ alg₂ alg₁≛alg₂ (prim op) = alg₁≛alg₂ op
fold-equiv′ alg₁ alg₂ alg₁≛alg₂ (done x) = refl
fold-equiv′ alg₁ alg₂ alg₁≛alg₂ (bind x q)
  rewrite fold-equiv′ alg₁ alg₂ alg₁≛alg₂ x
  rewrite fold-equiv′ alg₁ alg₂ alg₁≛alg₂ (q (foldFree alg₂ x))
  = refl

fullAdder-ref : (c x y : Bit) → Bit × Bit
fullAdder-ref c x y = (c ∧ x ∨ x ∧ y ∨ y ∧ c , x ⊕ y ⊕ c)

adder-ref : ∀ {n} → Bit → Vec Bit n → Vec Bit n → (Bit × Vec Bit n)
adder-ref c [] [] = c , []
adder-ref c (x ∷ xs) (y ∷ ys) =
  let (c′ , xys) = adder-ref (c ∧ x ∨ x ∧ y ∨ y ∧ c) xs ys
  in  c′ , (x ⊕ y ⊕ c) ∷ xys

module UnitypedExample where
  data Type : Set where
    bit : Type

  interpType : Type → Set
  interpType bit = Bit

  data Gate : List Type → List Type → Set where
    and or xor : Gate (bit ∷ bit ∷ []) [ bit ]
    high low : Gate [] [ bit ]

  interpGate : ∀ {as} → Op Gate interpType as → all interpType as
  interpGate (and ∙ (fst , snd)) = fst ∧ snd
  interpGate (or ∙ (fst , snd)) = fst ∨ snd
  interpGate (xor ∙ (fst , snd)) = fst ⊕ snd
  interpGate (high ∙ ∅) = one
  interpGate (low ∙ ∅) = zero

  open FreeDoNotation

  halfAdder : ∀ {⟦_⟧} → ⟦ bit ⟧ → ⟦ bit ⟧ → Free Gate ⟦_⟧ (⟦ bit ⟧ × ⟦ bit ⟧)
  halfAdder x y = do
    c ← prim (and ∙ x , y)
    xy ← prim (xor ∙ x , y)
    return (c , xy)

  fullAdder
    : ∀ {⟦_⟧}
    → ⟦ bit ⟧ → ⟦ bit ⟧ → ⟦ bit ⟧ → Free Gate ⟦_⟧ (⟦ bit ⟧ × ⟦ bit ⟧)
  fullAdder c x y = do
    c₀ , xy ← halfAdder x y
    c₁ , xyc ← halfAdder c xy
    c₂ ← prim (or ∙ c₀ , c₁)
    return (c₂ , xyc)

  adder
    : ∀ {⟦_⟧ n}
    → ⟦ bit ⟧
    → Vec ⟦ bit ⟧ n
    → Vec ⟦ bit ⟧ n
    → Free Gate ⟦_⟧ (⟦ bit ⟧ × Vec ⟦ bit ⟧ n)
  adder c [] [] = return (c , [])
  adder c (x ∷ xs) (y ∷ ys) = do
    c₁ , xy ← fullAdder c x y
    c₂ , xys ← adder c₁ xs ys
    return (c₂ , xy ∷ xys)

  fullAdder-spec
    : ∀ c x y
    → foldFree interpGate (fullAdder c x y) ≡
        (c ∧ x ∨ x ∧ y ∨ y ∧ c , (x ⊕ y ⊕ c))
  fullAdder-spec = exhaustion₃
    (λ c x y →
      foldFree interpGate (fullAdder c x y) ≡
        (c ∧ x ∨ x ∧ y ∨ y ∧ c , x ⊕ y ⊕ c))

  adder-spec
    : ∀ {n} c (xs ys : Vec Bit n)
    → foldFree interpGate (adder c xs ys) ≡
      adder-ref c xs ys
  adder-spec  c [] [] = refl
  adder-spec c (x ∷ xs) (y ∷ ys) =
    begin
      foldFree interpGate (adder c (x ∷ xs) (y ∷ ys))

    ≡⟨⟩
      foldFree interpGate (do
        c₁ , xy ← fullAdder c x y
        c₂ , xys ← adder c₁ xs ys
        return (c₂ , xy ∷ xys))

    ≡⟨⟩
      let (c₁ , xy) = foldFree interpGate (fullAdder c x y)
          (c₂ , xys) = foldFree interpGate (adder c₁ xs ys)
      in (c₂ , xy ∷ xys)

    ≡⟨ cong
         (λ (c₁ , xy) →
           let (c₂ , xys) = foldFree interpGate (adder c₁ xs ys)
           in  (c₂ , xy ∷ xys))
         (fullAdder-spec c x y) ⟩
      let c₁ = c ∧ x ∨ x ∧ y ∨ y ∧ c
          xy = x ⊕ y ⊕ c
          (c₂ , xys) = foldFree interpGate (adder c₁ xs ys)
      in  (c₂ , xy ∷ xys)

    ≡⟨ cong
         (λ (c₂ , xys) → (c₂ , (x ⊕ y ⊕ c) ∷ xys))
         (adder-spec (c ∧ x ∨ x ∧ y ∨ y ∧ c) xs ys) ⟩
      let c₁ = c ∧ x ∨ x ∧ y ∨ y ∧ c
          xy = x ⊕ y ⊕ c
          (c₂ , xys) = adder-ref c₁ xs ys
      in  (c₂ , xy ∷ xys)

    ≡⟨⟩
      let (c′ , xys) = adder-ref (c ∧ x ∨ x ∧ y ∨ y ∧ c) xs ys
      in  (c′ , (x ⊕ y ⊕ c) ∷ xys)

    ≡⟨⟩
      let (c′ , xys) = adder-ref c (x ∷ xs) (y ∷ ys)
      in  (c′ , xys)
    ∎
    where open ≡-Reasoning


module BitVecExample where
  data Type : Set where
    bit : Type
    bit⟨_⟩ : ℕ → Type

  interpType : Type → Set
  interpType bit = Bit
  interpType bit⟨ n ⟩ = Vec Bit n

  data Gate : List Type → List Type → Set where
    high low : Gate [] [ bit ]
    and or xor : Gate (bit ∷ bit ∷ []) [ bit ]
    head : ∀ {n} → Gate [ bit⟨ suc n ⟩ ] [ bit ]
    tail : ∀ {n} → Gate [ bit⟨ suc n ⟩ ] [ bit⟨ n ⟩ ]
    nil  : Gate [] [ bit⟨ zero ⟩ ]
    cons : ∀ {n} → Gate (bit ∷ bit⟨ n ⟩ ∷ []) [ bit⟨ suc n ⟩ ]

  interpGate : Alg Gate interpType
  interpGate (high ∙ ∅) = 1
  interpGate (low ∙ ∅) = 0
  interpGate (and ∙ x , y) = x ∧ y
  interpGate (or ∙ x , y) = x ∨ y
  interpGate (xor ∙ x , y) = x ⊕ y
  interpGate (head ∙ xs) = Data.Vec.head xs
  interpGate (tail ∙ xs) = Data.Vec.tail xs
  interpGate (nil ∙ ∅) = []
  interpGate (cons ∙ x , xs) = x ∷ xs

  embedType : UnitypedExample.Type → Type
  embedType UnitypedExample.bit = bit

  embedOp
    : ∀ {As Bs}
    → UnitypedExample.Gate As Bs
    → Gate (map embedType As) (map embedType Bs)
  embedOp UnitypedExample.and = and
  embedOp UnitypedExample.or = or
  embedOp UnitypedExample.xor = xor
  embedOp UnitypedExample.high = high
  embedOp UnitypedExample.low = low

  fullAdder : ∀ {⟦_⟧} → ⟦ bit ⟧ → ⟦ bit ⟧ → ⟦ bit ⟧ → Free Gate ⟦_⟧ (⟦ bit ⟧ × ⟦ bit ⟧)
  fullAdder c x y =
    mapFree embedType (ANF.mapOp embedType embedOp) (UnitypedExample.fullAdder c x y)

  fullAdder-spec
    : ∀ c x y
    → foldFree interpGate (fullAdder c x y) ≡ fullAdder-ref c x y
  fullAdder-spec c x y =
    begin
      foldFree interpGate (fullAdder c x y)

    ≡⟨⟩
      foldFree interpGate
        (mapFree embedType (ANF.mapOp embedType embedOp)
          (UnitypedExample.fullAdder c x y))

    ≡⟨ fold-map interpGate embedType
         (ANF.mapOp embedType embedOp)
         (UnitypedExample.fullAdder c x y) ⟩
      foldFree
        (interpGate ∘A ANF.mapOp embedType embedOp)
        (UnitypedExample.fullAdder c x y)

    ≡˘⟨ fold-cast
          (UnitypedExample.fullAdder c x y)
          (interpGate ∘A ANF.mapOp embedType embedOp)
          lemma₁ ⟩
      foldFree
        (castAlg lemma₁ (interpGate ∘A ANF.mapOp embedType embedOp))
        (castFree lemma₁ (UnitypedExample.fullAdder c x y))

    ≡⟨ fold-equiv′
         (castAlg lemma₁ (interpGate ∘A ANF.mapOp embedType embedOp))
         UnitypedExample.interpGate
         lemma₃
         (UnitypedExample.fullAdder c x y) ⟩
      foldFree
        UnitypedExample.interpGate
        (castFree lemma₁ (UnitypedExample.fullAdder c x y))

    -- Cheat the parametricity step by letting it just normalize
    -- entirely instead of using a general parametricity lemma about
    -- fullAdder.
    ≡⟨⟩
      foldFree UnitypedExample.interpGate (UnitypedExample.fullAdder c x y)

    ≡⟨ UnitypedExample.fullAdder-spec c x y ⟩
      fullAdder-ref c x y
    ∎
   where
    open ≡-Reasoning

    lemma₁ : UnitypedExample.interpType ≗ interpType ∘ embedType
    lemma₁ UnitypedExample.bit = refl

    lemma₂a
      : ∀ x xs
      → all UnitypedExample.interpType (x ∷ xs) ≡
          all (interpType ∘ embedType) (x ∷ xs)
    lemma₂a x [] = lemma₁ x
    lemma₂a x (x₁ ∷ xs) rewrite lemma₁ x rewrite lemma₂a x₁ xs = refl

    lemma₂ : all UnitypedExample.interpType ≗ all (interpType ∘ embedType)
    lemma₂ [] = refl
    lemma₂ (x ∷ xs) = lemma₂a x xs

    lemma₃
      : ∀ {As}
      → (op : Op UnitypedExample.Gate UnitypedExample.interpType As)
      → castAlg lemma₁ (interpGate ∘A ANF.mapOp embedType embedOp) op ≡
          UnitypedExample.interpGate op
    lemma₃ (UnitypedExample.and ∙ args) = refl
    lemma₃ (UnitypedExample.or ∙ args) = refl
    lemma₃ (UnitypedExample.xor ∙ args) = refl
    lemma₃ (UnitypedExample.high ∙ args) = refl
    lemma₃ (UnitypedExample.low ∙ args) = refl

  open FreeDoNotation

  adder
    : ∀ {n ⟦_⟧}
    → ⟦ bit ⟧ → ⟦ bit⟨ n ⟩ ⟧ → ⟦ bit⟨ n ⟩ ⟧ → Free Gate ⟦_⟧ (⟦ bit ⟧ × ⟦ bit⟨ n ⟩ ⟧)
  adder {zero} c x y = do
    xy ← prim (nil ∙ ∅)
    return (c , xy)
  adder {suc n} c xs₀ ys₀ = do
    x ← prim (head ∙ xs₀)
    xs ← prim (tail ∙ xs₀)
    y ← prim (head ∙ ys₀)
    ys ← prim (tail ∙ ys₀)
    c′ , xy ← fullAdder c x y
    c″ , xys ← adder c′ xs ys
    xys₀ ← prim (cons ∙ xy , xys)
    return (c″ , xys₀)

  adder-spec
    : ∀ {n : ℕ} c (xs ys : Vec Bit n)
    → foldFree interpGate (adder c xs ys) ≡ adder-ref c xs ys
  adder-spec {zero} c [] [] = refl
  adder-spec {suc n} c (x ∷ xs) (y ∷ ys) =
    begin
      foldFree interpGate (adder c (x ∷ xs) (y ∷ ys))
    ≡⟨⟩
      let (c′ , xy) = foldFree interpGate (fullAdder c x y)
          (c″ , xys) = foldFree interpGate (adder c′ xs ys)
      in  c″ , xy ∷ xys
    ≡⟨ cong
         (λ (c′ , xy) →
            let c″ , xys = foldFree interpGate (adder c′ xs ys)
            in c″ , xy ∷ xys)
         (fullAdder-spec c x y) ⟩
      let (c′ , xy) = (c ∧ x ∨ x ∧ y ∨ y ∧ c , x ⊕ y ⊕ c)
          (c″ , xys) = foldFree interpGate (adder c′ xs ys)
      in  (c″ , xy ∷ xys)
    ≡⟨ cong
         (λ (c′ , xys) → c′ , (x ⊕ y ⊕ c) ∷ xys)
         (adder-spec (c ∧ x ∨ x ∧ y ∨ y ∧ c) xs ys) ⟩
      let (c′ , xys) = adder-ref (c ∧ x ∨ x ∧ y ∨ y ∧ c) xs ys
      in  (c′ , (x ⊕ y ⊕ c) ∷ xys)
    ≡⟨⟩
      adder-ref c (x ∷ xs) (y ∷ ys)
    ∎
   where open ≡-Reasoning
