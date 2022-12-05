module Experiments.NetPHOAS where

-- A "parametric HOAS" style representation of combinational circuits.
-- (Note Agda rejects traditional HOAS because it's not "strictly
-- positive".)
--
-- This representation:
--
-- * deals only in individual bits, i.e. has no compound types or multi-bit buses
-- * is unityped, i.e. has no internal type system
-- * is fully flattened to primitive gates, i.e. retains no hierarchy
-- * encodes sharing in an ANF-style structure
-- * encodes variable binding with PHOAS
--
-- Pros:
--
-- * it's reasonably convenient to construct: the type of
--   variables doesn't change when progressing deeper into the structure
-- * it's easy to inspect given an algebra over the primitive gates
--
-- Cons:
--
-- * flattening all hierarchy probably makes it hard to manage in proofs
-- * flattening all hierarchy means repeated structures have needlessly large
--   representations
-- * flattening all types to booleans means the interface of a circuit is clumsy
-- * unlike a de bruijn encoding, it's not "plain data"
-- * may be difficult to convert to de bruijn (or is that a deficiency of de bruijn?)


open import Level using (_⊔_)
open import Function using (_∘_; _$_; id; λ-)
open import Data.Fin using (Fin; zero)
open import Data.Fin.Show using (show)
open import Data.String using (String; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; _∷_; []; [_]; lookup; replicate; splitAt; tabulate)
open import Relation.Binary.PropositionalEquality using
  ( _≡_; refl; cong; sym; trans
  ; module ≡-Reasoning
  )
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Setoid-Reasoning

open import Data.Bit using (Bit; zero; one; _↑_; _∧_; _∨_; _⊕_)
open import Data.Bit.Properties using (⊕-assoc; ∨-identityʳ)
open import Data.Finite using ()
open import Experiments.Gate hiding (map)
open import Tactic.Exhaustion using (exhaustion₂; exhaustion₃)

data Comb (G : Set → ℕ → Set) (V : Set) (n : ℕ) : Set where
  return : Vec V n → Comb G V n
  bind : ∀ {k} → (g : G V k) → (q : Vec V k → Comb G V n) → Comb G V n

-- Slow substitution of one circuit into another.  The Builder monad
-- defined below effectively right-associates chains of 'subst's to
-- avoid repeated traversals in left-associated chains.
subst : ∀ {G V m n} → Comb G V m → (Vec V m → Comb G V n) → Comb G V n
subst (return x) p = p x
subst (bind g q) p = bind g λ xs → subst (q xs) p

evalComb : ∀ {A : Set} {_⇒_ n} → (∀ {k} → A ⇒ k → Vec A k) → Comb _⇒_ A n → Vec A n
evalComb f (return x) = x
evalComb f (bind x q) = evalComb f (q (f x))

_⇒_ : ∀ {a b} {A : Set a} (P Q : A → Set b) → Set (a ⊔ b)
P ⇒ Q = ∀ {x} → P x → Q x

_≋[_]_ : ∀ {G V n} (x : Comb G V n) → (eval : G V ⇒ Vec V) → (y : Comb G V n) → Set
x ≋[ eval ] y = evalComb eval x ≡ evalComb eval y

module Under {G V n} (eval : G V ⇒ Vec V) where
  private _≋[]_ : (x y : Comb G V n) → Set
  x ≋[] y = x ≋[ eval ] y

  ≋[_]-refl : ∀ {x} → x ≋[] x
  ≋[_]-refl = refl

  ≋[_]-sym : ∀ {x y} → x ≋[] y → y ≋[] x
  ≋[_]-sym = sym

  ≋[_]-trans : ∀ {x y z} → x ≋[] y → y ≋[] z → x ≋[] z
  ≋[_]-trans = trans

  ≋[_]-Equiv : IsEquivalence _≋[]_
  ≋[_]-Equiv = record { refl = refl ; sym = sym ; trans = trans }

  ≋[_]-Setoid : Setoid _ _
  ≋[_]-Setoid = record { Carrier = Comb G V n ; _≈_ = _≋[]_ ; isEquivalence = ≋[_]-Equiv }

module _ {G V n} where
  _≋′_ : (x y : Comb G V n) → Set
  x ≋′ y = (eval : G V ⇒ Vec V) → x ≋[ eval ] y

  record _≋_ (x y : Comb G V n) : Set where
    field
      inst : x ≋′ y

  open _≋_ renaming (inst to ≋-inst) public

  ≋-refl : ∀ {x} → x ≋ x
  ≋-refl = record { inst = λ- refl }

  ≋-sym : ∀ {x y} → x ≋ y → y ≋ x
  ≋-sym x≋y = record { inst = λ eval → sym (≋-inst x≋y eval) }

  ≋-trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z
  ≋-trans x≋y y≋z = record { inst = λ eval → trans (≋-inst x≋y eval) (≋-inst y≋z eval) }

  ≋-Equiv : IsEquivalence _≋_
  ≋-Equiv = record { refl = ≋-refl ; sym = ≋-sym ; trans = ≋-trans }

  ≋-Setoid : Setoid _ _
  ≋-Setoid = record { Carrier = Comb G V n ; _≈_ = _≋_ ; isEquivalence = ≋-Equiv }

  module ≋-Reasoning = Setoid-Reasoning ≋-Setoid

  ≋-ext : ∀ {x y} → (∀ {eval : G V ⇒ Vec V} → x ≋[ eval ] y) → x ≋ y
  ≋-ext f = record { inst = λ- f }

subst-return
  : ∀ {G V n} (c : Comb G V n) → subst c return ≋ c
subst-return (return x) = record { inst = λ- refl }
subst-return (bind g q) = record { inst = λ eval → ≋-inst (subst-return (q (eval g))) eval }

unsubst
  : ∀ {G V m n} (c : Comb G V n) (p : Vec V n → Comb G V m)
  → (eval : ∀ {k} → G V k → Vec V k)
  → evalComb eval (subst c p) ≡ evalComb eval (p (evalComb eval c))
unsubst (return x) p eval = refl
unsubst (bind g q) p eval = unsubst (q (eval g)) p eval

cong-subst
  : ∀ {G V n m} {x y : Comb G V n} (q : Vec V n → Comb G V m)
  → x ≋ y → subst x q ≋ subst y q
cong-subst {x = x} {y = y} q x≋y = record
  { inst = λ eval →
      begin
        evalComb eval (subst x q)
      ≡⟨ unsubst x q eval ⟩
        evalComb eval (q (evalComb eval x))
      ≡⟨ cong (evalComb eval ∘ q) (≋-inst x≋y eval) ⟩
        evalComb eval (q (evalComb eval y))
      ≡⟨ sym (unsubst y q eval) ⟩
        evalComb eval (subst y q)
      ∎
  }
 where
  open ≡-Reasoning

module DiffComb where
  RawDiffComb : (Set → ℕ → Set) → Set → ℕ → Set
  RawDiffComb G V n = ∀ {m} → (Vec V n → Comb G V m) → Comb G V m

  Coherent : ∀ {G V n} → RawDiffComb G V n → Set
  Coherent {G} {V} {n} dc =
    ∀ {m} (q : Vec V n → Comb G V m)
    → dc q ≋ subst (dc return) q

  record DiffComb (G : Set → ℕ → Set) (V : Set) (n : ℕ) : Set where
    field
      apply : RawDiffComb G V n
      coherent : Coherent apply

  open DiffComb using (apply; coherent) public

  fromComb : ∀ {G V n} → Comb G V n → DiffComb G V n
  fromComb c = record
    { apply = subst c
    ; coherent = λ q → cong-subst q (≋-sym (subst-return c))
    }

  factor
    : ∀ {G V m n} (x : DiffComb G V n)
    → (q : Vec V n → Comb G V m)
    → (eval : G V ⇒ Vec V)
    → apply x q ≋[ eval ] q (evalComb eval (apply x return))
  factor x q eval = trans (≋-inst (coherent x q) eval) (unsubst (apply x return) q eval)

  _>>=_ : ∀ {G V m n} → DiffComb G V n → (Vec V n → DiffComb G V m) → DiffComb G V m
  _>>=_ {G} {V} {m} {n} x f = record
    { apply = λ q → apply x (λ xs → apply (f xs) q)
    ; coherent = λ {k} q → ≋-ext {G} $ λ {eval} →
        let open Setoid-Reasoning (Under.≋[_]-Setoid {G} {V} {k} eval) in
        begin
          apply x (λ xs → apply (f xs) q)

        ≈⟨ factor x (λ xs → apply (f xs) q) eval ⟩
          let xs = evalComb eval (apply x return) in apply (f xs) q

        ≈⟨ factor (f (evalComb eval (apply x return))) q eval ⟩
          let xs = evalComb eval (apply x return)
              ys = evalComb eval (apply (f xs) return)
          in  q ys

        ≈˘⟨ cong (evalComb eval ∘ q) (factor x (λ xs → apply (f xs) return) eval) ⟩
          let ys = evalComb eval (apply x (λ xs → apply (f xs) return))
          in  q ys

        ≈⟨ sym (unsubst (apply x (λ xs → apply (f xs) return)) q eval) ⟩
          subst (apply x (λ xs → apply (f xs) return)) q
        ∎
    }

  toComb : ∀ {G V n} → DiffComb G V n → Comb G V n
  toComb dc = DiffComb.apply dc return

_!_ : ∀ {A : Set} {n} → Vec A n → Fin n → A
_!_ = lookup

gate₁′ : ∀ {A : Set} {n} {_⇒_} → A ⇒ 1 → (A → Comb _⇒_ A n) → Comb _⇒_ A n
gate₁′ g f = bind g (f ∘ (_! zero))

return₁ : ∀ {A : Set} {_⇒_} → A → Comb _⇒_ A 1
return₁ = return ∘ [_]

inv′ : ∀ {A : Set} {n} → A → (A → Comb Gate A n) → Comb Gate A n
inv′ x = gate₁′ (NAND x x)

and′ : ∀ {A : Set} {n} → A → A → (A → Comb Gate A n) → Comb Gate A n
and′ x y q = gate₁′ (NAND x y) λ x∙y → inv′ x∙y q

and-correct : ∀ x y → evalComb evalGate (and′ x y return₁) ≡ [ x ∧ y ]
and-correct = exhaustion₂ _

record Builder (_⇒_ : Set → ℕ → Set) (V A : Set) : Set where
  field
    run : ∀ {n} → (q : A → Comb _⇒_ V n) → Comb _⇒_ V n

gate : ∀ {V : Set} {_⇒_} {n} → V ⇒ n → Builder _⇒_ V (Vec V n)
Builder.run (gate g) q = bind g q

pure : ∀ {V A : Set} {_⇒_} → A → Builder _⇒_ V A
Builder.run (pure x) q = q x

_>>=_ : ∀ {V A B : Set} {_⇒_} → Builder _⇒_ V A → (A → Builder _⇒_ V B) → Builder _⇒_ V B
Builder.run (b >>= f) q =
  Builder.run b λ x →
  Builder.run (f x) λ y →
  q y

join : ∀ {V A : Set} {G} → Builder G V (Builder G V A) → Builder G V A
Builder.run (join b) q = Builder.run b (λ b′ → Builder.run b′ q )

map _<$>_ : ∀ {V A B : Set} {_⇒_} → (A → B) → Builder _⇒_ V A → Builder _⇒_ V B
map f b = record { run = λ q → Builder.run b (q ∘ f) }

infixl 20 _<$>_ _<*>_ _=*<_

_<*>_ : ∀ {V A B : Set} {G} → Builder G V (A → B) → Builder G V A → Builder G V B
Builder.run (bf <*> ba) q = Builder.run bf λ f → Builder.run ba λ x → q (f x)

_=*<_ : ∀ {V A B : Set} {G} → Builder G V (A → Builder G V B) → Builder G V A → Builder G V B
Builder.run (bf =*< ba) q = Builder.run bf (λ f → Builder.run ba (λ x → Builder.run (f x) q))

_<$>_ = map

build : ∀ {V : Set} {G n} → Builder G V (Vec V n) → Comb G V n
build b = Builder.run b return

build₁ : ∀ {V : Set} {G} → Builder G V V → Comb G V 1
build₁ = build ∘ map [_]

gate₁ : ∀ {V : Set} {G} → G V 1 → Builder G V V
gate₁ = map (_! zero) ∘ gate

nand and or xor : ∀ {V : Set} → V → V → Builder Gate V V

inv : ∀ {V : Set} → V → Builder Gate V V
inv x = nand x x

nand x y = gate₁ (NAND x y)
and x y = nand x y >>= inv
or x y = nand <$> inv x =*< inv y
xor x y = do
  xy ← nand x y
  nand <$> nand x xy =*< nand xy y

𝟎 𝟏 : ∀ {V} → Builder Gate V V
𝟎 = gate₁ low
𝟏 = gate₁ high

halfAdder : ∀ {V : Set} → V → V → Builder Gate V (V × V)
halfAdder x y = _,_ <$> xor x y <*> and x y

fullAdder : ∀ {V : Set} → V → V → V → Builder Gate V (V × V)
fullAdder x y c = do
  xy , c₀ ← halfAdder x y
  r , c₁ ← halfAdder xy c
  (r ,_) <$> or c₀ c₁

-- Vec V n is lsb ∷ msbs
adder : ∀ {V : Set} {n} → V → Vec V n → Vec V n → Builder Gate V (Vec V (suc n))
adder c [] [] = pure [ c ]
adder c (x₀ ∷ xs) (y₀ ∷ ys) = do
  xy₀ , c₀ ← fullAdder x₀ y₀ c
  xy ← adder c₀ xs ys
  pure (xy₀ ∷ xy)

gateCount′ : ∀ {G n} → Comb G ⊤ n → ℕ
gateCount′ (return x) = 0
gateCount′ (bind g c) = suc (gateCount′ (c (replicate tt)))

gateCount : ∀ {G m n} → (∀ {V} → Vec V n → Comb G V m) → ℕ
gateCount cf = gateCount′ (cf (replicate tt))

example : ∀ {V} n → Vec V (suc (n + n)) → Comb Gate V (suc n)
example n (b ∷ bs) with (x , y , _) ← splitAt n bs = build $
  (𝟎 >>= λ c → adder c x y)

depth : ∀ {m n} → (∀ {V} → Vec V n → Comb Gate V m) → Vec ℕ m
depth {G} {m} c = go (c (replicate 0))
 where
  go : ∀ {n} → Comb Gate ℕ n → Vec ℕ n
  go (return x) = x
  go (bind g cf) = go (cf (gateDepth g))

-- Just for fun: if we unfolded the circuit to a tree (duplicating all
-- shared nodes), how many gates would be in that tree?
treeSize : ∀ {m n} → (∀ {V} → Vec V n → Comb Gate V m) → Vec ℕ m
treeSize cf = evalComb gateTreeSize (cf (replicate 0))

formatTree : ∀ {m n} → (∀ {V} → Vec V n → Comb Gate V m) → Vec String m
formatTree cf = Data.Vec.map (_$ 0) $
  evalComb formatGateTree (cf (tabulate λ i p → "x" ++ show i))

adder-ref : ∀ {n} → Bit → Vec Bit n → Vec Bit n → Vec Bit (suc n)
adder-ref c [] [] = [ c ]
adder-ref c (x ∷ xs) (y ∷ ys) = (x ⊕ y ⊕ c) ∷ (adder-ref (x ∧ y ∨ x ∧ c ∨ y ∧ c) xs ys)

_≡[_at_]_
  : ∀ {A G V m}
  → Builder G V A
  → (∀ {k} → G V k → Vec V k)
  → (A → Comb G V m)
  → Builder G V A → Set
x ≡[ eval at q ] y = evalComb eval (Builder.run x q) ≡ evalComb eval (Builder.run y q)

_≡[_]_ : ∀ {A G V} → Builder G V A → (∀ {k} → G V k → Vec V k) → Builder G V A → Set
_≡[_]_ {A} {G} {V} x eval y =
  ∀ {m} (q : A → Comb G V m) → x ≡[ eval at q ] y

{-
module Under {V : Set} (G : Set → ℕ → Set) (eval : ∀ {k} → G V k → Vec V k) where
  record _≈_ {A} (x y : Builder G V A) : Set where
    field
      inst-≈ : x ≡[ eval ] y

  open _≈_ public

  infixr 4 _↝_
  _↝_ : ∀ {A} (x : Builder G V A) (y : A) → Set
  x ↝ y = x ≈ pure y

  ≈-refl : ∀ {A} {x : Builder G V A} → x ≈ x
  inst-≈ ≈-refl q = refl

  ≈-sym : ∀ {A} {x y : Builder G V A} → x ≈ y → y ≈ x
  inst-≈ (≈-sym x≈y) q = sym (inst-≈ x≈y q)

  ≈-trans : ∀ {A} {x y z : Builder G V A} → x ≈ y → y ≈ z → x ≈ z
  inst-≈ (≈-trans x≈y y≈z) q = trans (inst-≈ x≈y q) (inst-≈ y≈z q)

  ≈-Equiv : ∀ {A} →  IsEquivalence (_≈_ {A})
  ≈-Equiv = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

  ≈-Setoid : ∀ {A} → Setoid _ _
  ≈-Setoid {A} = record { Carrier = Builder G V A ; _≈_ = _≈_ ; isEquivalence = ≈-Equiv }

  module ≈-Reasoning {A} = Setoid-Reasoning (≈-Setoid {A})

  cong->>=
    : ∀ {A B} {x y : Builder G V A} (f : A → Builder G V B)
    → x ≈ y → (x >>= f) ≈ (y >>= f)
  inst-≈ (cong->>= f x≈y) q = inst-≈ x≈y (λ x₁ → Builder.run (f x₁) q)

  cong-<$>
    : ∀ {A B} {x y : Builder G V A} (f : A → B)
    → x ≈ y → (f <$> x) ≈ (f <$> y)
  cong-<$> f x≈y = record { inst-≈ = λ q → inst-≈ x≈y (q ∘ f) }

{-
  cong-<*>
    : ∀ {A B} {x y : Builder G V A} (f : Builder G V (A → B))
    → x ≈ y → (f <*> x) ≈ (f <*> y)
  cong-<*> f x≈y = record { inst-≈ = λ q → {!!} }
  -}

  -- In a context where the lhs and rhs builders are inferrable
  -- (e.g. inside _≈⟨_⟩_), tries to deduce the equivalence
  -- automatically pointwise.
  ≈-compute
    : ∀ {A} {x y : Builder G V A}
    → {{(∀ {m} {q : A → Comb G V m} → x ≡[ eval at q ] y)}}
    → x ≈ y
  ≈-compute {{f}} = record { inst-≈ = λ q → f {q = q} }

  eval->>=
    : ∀ {A B} {x : Builder G V A} {y} (f : A → Builder G V B)
    → x ↝ y → (x >>= f) ≈ f y
  eval->>= f x↝y = ≈-trans (cong->>= f x↝y) ≈-compute


module _ where
  open Under Gate evalGate

  open ≈-Reasoning

  xor-spec : ∀ x y → xor x y ↝ x ⊕ y
  xor-spec x y =
    begin
      xor x y
    ≈⟨ ≈-compute ⟩
      pure (x ↑ (x ↑ y) ↑ (x ↑ y ↑ y))
    ≡⟨ cong pure (lemma x y) ⟩
      pure (x ⊕ y)
    ∎
   where
    lemma : ∀ x y → x ↑ (x ↑ y) ↑ (x ↑ y ↑ y) ≡ x ⊕ y
    lemma zero zero = refl
    lemma zero one = refl
    lemma one zero = refl
    lemma one one = refl

  and-spec : ∀ x y → and x y ↝ x ∧ y
  and-spec x y =
    begin
      and x y
    ≈⟨ ≈-compute ⟩
      pure (x ↑ y ↑ (x ↑ y))
    ≡⟨ cong pure (lemma x y) ⟩
      pure (x ∧ y)
    ∎
   where
    lemma : ∀ x y → (x ↑ y) ↑ (x ↑ y) ≡ x ∧ y
    lemma zero zero = refl
    lemma zero one = refl
    lemma one zero = refl
    lemma one one = refl

  or-spec : ∀ x y → or x y ↝ x ∨ y
  or-spec x y =
    begin
      or x y
    ≈⟨ ≈-compute ⟩
      pure (x ↑ x ↑ (y ↑ y))
    ≡⟨ cong pure (lemma x y) ⟩
      pure (x ∨ y)
    ∎
   where
    lemma : ∀ x y → (x ↑ x) ↑ (y ↑ y) ≡ x ∨ y
    lemma zero zero = refl
    lemma zero one = refl
    lemma one zero = refl
    lemma one one = refl

  halfAdder-spec : ∀ x y → halfAdder x y ↝ x ⊕ y , x ∧ y
  halfAdder-spec x y =
    begin
      halfAdder x y
    ≡⟨⟩
      _,_ <$> xor x y <*> and x y

    ≈⟨ ≈-compute ⟩
      (do
        xy ← xor x y
        c ← and x y
        pure (xy , c))

    ≈⟨ eval->>=
         (λ xy →
           do
             c ← and x y
             pure (xy , c))
          (xor-spec x y) ⟩
      (do
        c ← and x y
        pure (x ⊕ y , c))

    ≈⟨ eval->>=
         (λ c → pure (x ⊕ y , c))
          (and-spec x y) ⟩
      pure (x ⊕ y , x ∧ y)

    ∎

  fullAdder-spec : ∀ x y c → fullAdder x y c ≈ pure (x ⊕ y ⊕ c , x ∧ y ∨ x ∧ c ∨ y ∧ c)
  fullAdder-spec x y c =
    begin
      fullAdder x y c
    ≡⟨⟩
      (do
        xy , c₀ ← halfAdder x y
        r , c₁ ← halfAdder xy c
        (r ,_) <$> or c₀ c₁)

    ≈⟨ eval->>=
         (λ { (xy , c₀) →
           do
             r , c₁ ← halfAdder xy c
             (r ,_) <$> or c₀ c₁})
         (halfAdder-spec x y) ⟩
      (do
        r , c₁ ← halfAdder (x ⊕ y) c
        (r ,_) <$> or (x ∧ y) c₁)

    ≈⟨ eval->>=
         (λ { (r , c₁) → (r ,_) <$> or (x ∧ y) c₁ })
         (halfAdder-spec (x ⊕ y) c) ⟩
      (do
        c′ ← or (x ∧ y) ((x ⊕ y) ∧ c)
        pure ((x ⊕ y) ⊕ c , c′))

    ≈⟨ eval->>=
         (λ c′ → pure ((x ⊕ y) ⊕ c , c′))
         (or-spec (x ∧ y) ((x ⊕ y) ∧ c)) ⟩
      pure ((x ⊕ y) ⊕ c , x ∧ y ∨ (x ⊕ y) ∧ c)

    ≡⟨ cong (pure ∘ (_, x ∧ y ∨ (x ⊕ y) ∧ c)) (⊕-assoc x y c) ⟩
      pure (x ⊕ y ⊕ c , x ∧ y ∨ (x ⊕ y) ∧ c)

    ≡⟨ cong (pure ∘ (x ⊕ y ⊕ c ,_)) (lemma x y c) ⟩
      pure (x ⊕ y ⊕ c , x ∧ y ∨ x ∧ c ∨ y ∧ c)

    ∎
   where
    lemma : ∀ x y c → x ∧ y ∨ (x ⊕ y) ∧ c ≡ x ∧ y ∨ x ∧ c ∨ y ∧ c
    lemma zero y c = refl
    lemma one zero c = sym (∨-identityʳ c)
    lemma one one c = refl

  adder-spec : ∀ {n} c (xs ys : Vec Bit n) → adder c xs ys ≈ pure (adder-ref c xs ys)
  adder-spec c [] [] = ≈-refl
  adder-spec c (x ∷ xs) (y ∷ ys) =
    begin
      adder c (x ∷ xs) (y ∷ ys)
    ≡⟨⟩
      (do
        xy₀ , c₀ ← fullAdder x y c
        xy ← adder c₀ xs ys
        pure (xy₀ ∷ xy))

    ≈⟨ eval->>=
         (λ { (xy₀ , c₀) →
           do
             xy ← adder c₀ xs ys
             pure (xy₀ ∷ xy) })
         (fullAdder-spec x y c) ⟩
      (do
        xy ← adder (x ∧ y ∨ x ∧ c ∨ y ∧ c) xs ys
        pure ((x ⊕ y ⊕ c) ∷ xy))

    ≈⟨ eval->>=
         (λ xy → pure ((x ⊕ y ⊕ c) ∷ xy))
         (adder-spec (x ∧ y ∨ x ∧ c ∨ y ∧ c) xs ys) ⟩
      pure ((x ⊕ y ⊕ c) ∷ adder-ref (x ∧ y ∨ x ∧ c ∨ y ∧ c) xs ys)

    ≡⟨⟩
      pure (adder-ref c (x ∷ xs) (y ∷ ys))

    ∎
    -}

-- 'b' builds a circuit that reduces to 'x' under 'eval'.
--
-- This is technically but not practically more powerful than saying
-- that evaluating the circuit gives 'x': this also proves that, in
-- the context of a larger circuit, this circuit is equivalent to the
-- given value.
_⇓[_]_ : ∀ {A G V} → Builder G V A → (∀ {k} → G V k → Vec V k) → A → Set
_⇓[_]_ {A} {G} {V} b eval x = b ≡[ eval ] pure x

to-≡
  : ∀ {n G V} {b : Builder G V (Vec V n)} {x} {eval : ∀ {k} → G V k → Vec V k}
  → b ⇓[ eval ] x → evalComb eval (build b) ≡ x
to-≡ prf = prf return

adder-spec′
  : ∀ {n} c (xs ys : Vec Bit n)
  → adder c xs ys ⇓[ evalGate ] adder-ref c xs ys
adder-spec′ c [] [] q = refl
adder-spec′ c (x ∷ xs) (y ∷ ys) q =
  begin
    evalComb evalGate (Builder.run (adder c (x ∷ xs) (y ∷ ys)) q)
  ≡⟨⟩
    evalComb evalGate (Builder.run (adder (c′ x y c) xs ys) q′)
  ≡⟨ adder-spec′ (c′ x y c) xs ys q′ ⟩
    evalComb evalGate (q′ (adder-ref (c′ x y c) xs ys))
  ≡⟨⟩
    evalComb evalGate (q (xy₀ x y c ∷ adder-ref (c′ x y c) xs ys))
  ≡⟨ cong (λ xyc → evalComb evalGate (q (xyc ∷ adder-ref (c′ x y c) xs ys)))
          (xy₀-matches x y c) ⟩
    evalComb evalGate (q ((x ⊕ y ⊕ c) ∷ adder-ref (c′ x y c) xs ys))
  ≡⟨ cong
       (λ cc → evalComb evalGate (q ((x ⊕ y ⊕ c) ∷ adder-ref cc xs ys))) (c′-matches x y c) ⟩
    evalComb evalGate (q ((x ⊕ y ⊕ c) ∷ adder-ref (x ∧ y ∨ x ∧ c ∨ y ∧ c) xs ys))
  ≡⟨⟩
    evalComb evalGate (q (adder-ref c (x ∷ xs) (y ∷ ys)))
  ∎
 where
  open ≡-Reasoning

  c′ : Bit → Bit → Bit → Bit
  c′ x y c = x ↑ y ↑ (x ↑ y) ↑ (x ↑ y ↑ (x ↑ y)) ↑
         (x ↑ (x ↑ y) ↑ (x ↑ y ↑ y) ↑ c ↑ (x ↑ (x ↑ y) ↑ (x ↑ y ↑ y) ↑ c) ↑
          (x ↑ (x ↑ y) ↑ (x ↑ y ↑ y) ↑ c ↑ (x ↑ (x ↑ y) ↑ (x ↑ y ↑ y) ↑ c)))

  xy₀ : Bit → Bit → Bit → Bit
  xy₀ x y c = x ↑ (x ↑ y) ↑ (x ↑ y ↑ y) ↑ (x ↑ (x ↑ y) ↑ (x ↑ y ↑ y) ↑ c) ↑
          (x ↑ (x ↑ y) ↑ (x ↑ y ↑ y) ↑ c ↑ c)

  xy₀-matches : (x y c : Bit) → xy₀ x y c ≡ x ⊕ y ⊕ c
  xy₀-matches = exhaustion₃ _

  c′-matches : (x y c : Bit) → c′ x y c ≡ x ∧ y ∨ x ∧ c ∨ y ∧ c
  c′-matches = exhaustion₃ _

  q′ : _ → Comb Gate Bit _
  q′ = λ xy → q (xy₀ x y c ∷ xy)
