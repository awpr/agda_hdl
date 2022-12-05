module Data.Finite where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Fin.Properties using (remQuot-combine; combine-remQuot)
open import Data.Nat using (ℕ; _*_)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.Vec.Relation.Unary.All as All using (All)
open import Function using (case_of_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (_↔_; Inverse; id)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; →-to-⟶; module ≡-Reasoning)

open import Instances

-- I think there's no point in level-polymorphism here because any
-- type that can't be in Set must involve Set, which is infinite.
record IsFinite (A : Set) : Set where
  field
    cardinality : ℕ
    iso : A ↔ Fin cardinality

  fromFin : Fin cardinality → A
  fromFin = Inverse.from iso ⟨$⟩_

  toFin : A → Fin cardinality
  toFin = Inverse.to iso ⟨$⟩_

  enumerate : Vec A cardinality
  enumerate = tabulate fromFin

  lookup∘enumerate
    : (i : Fin cardinality)
    → Data.Vec.lookup enumerate i ≡ fromFin i
  lookup∘enumerate i = lookup∘tabulate fromFin i

  all
    : ∀ {a} (P : A → Set a)
    → All P enumerate
    → (x : A) → P x
  all P ps x with All.lookup (toFin x) ps
  ... | px
    rewrite lookup∘enumerate (toFin x)
    rewrite Inverse.left-inverse-of iso x
    =  px

private fin-1-is-zero : ∀ (x : Fin 1) → x ≡ zero
fin-1-is-zero zero = refl

∥_∥ : ∀ A → {{IsFinite A}} → ℕ
∥ A ∥ {{finA}} = IsFinite.cardinality finA

-- Note '{{_ : ...}}' actually makes a difference: it causes the
-- instance to be in scope in the rest of the signature, so it can be
-- solved when needed by '∥ A ∥'.
enumerate : ∀ {A} → {{_ : IsFinite A}} → Vec A ∥ A ∥
enumerate {{finA}} = IsFinite.enumerate finA

toFin : ∀ {A} → {{_ : IsFinite A}} → A → Fin ∥ A ∥
toFin {{finA}} x = IsFinite.toFin finA x

fromFin : ∀ {A} → {{_ : IsFinite A}} → Fin ∥ A ∥ → A
fromFin {{finA}} x = IsFinite.fromFin finA x


instance
  finite-⊤ : IsFinite ⊤
  finite-⊤ = record
    { cardinality = 1
    ; iso = record
        { to = record { _⟨$⟩_ = λ x → Fin.zero ; cong = λ _ → refl }
        ; from = record { _⟨$⟩_ = λ x → tt ; cong = λ _ → refl }
        ; inverse-of = record
            { left-inverse-of = λ x → refl
            ; right-inverse-of = λ x → sym (fin-1-is-zero x)
            }
        }
    }

  finite-⊥ : IsFinite ⊥
  finite-⊥ = record
    { cardinality = 0
    ; iso = record
        { to = →-to-⟶ ⊥-elim
        ; from = →-to-⟶ λ ()
        ; inverse-of = record
            { left-inverse-of = λ ()
            ; right-inverse-of = λ ()
            }
        }
    }

  finite-Fin : ∀ {n} → IsFinite (Fin n)
  finite-Fin {n} = record
    { cardinality = n
    ; iso = id
    }

  finite-Bool : IsFinite Bool
  finite-Bool = record
    { cardinality = 2
    ; iso = record
        { to = →-to-⟶ λ { false → 0 ; true → 1 }
        ; from = →-to-⟶ λ { zero → false ; (suc zero) → true }
        ; inverse-of = record
            { left-inverse-of = λ { false → refl ; true → refl }
            ; right-inverse-of = λ { zero → refl ; (suc zero) → refl }
            }
        }
    }

  finite-× : ∀ {A B} → {{IsFinite A}} → {{IsFinite B}} → IsFinite (A × B)
  finite-× {A} {B} {{finA}} {{finB}} = record
    { cardinality = ∥ A ∥ * ∥ B ∥
    ; iso = record
        { to = →-to-⟶ λ { (x , y) → Fin.combine (toFin x) (toFin y) }
        ; from = →-to-⟶ λ xy →
            let (x , y) = Fin.remQuot ∥ B ∥ xy
            in  fromFin x , fromFin y
        ; inverse-of = record
            { left-inverse-of = λ where
                (x , y) →
                  begin
                    let x′ , y′ = Fin.remQuot ∥ B ∥
                          (Fin.combine (toFin x) (toFin y))
                    in  fromFin x′ , fromFin y′

                  ≡⟨ cong
                       (λ { (x′ , y′) → fromFin x′ , fromFin y′ })
                       (remQuot-combine (toFin x) (toFin y)) ⟩
                    fromFin (toFin x) , fromFin (toFin y)

                  ≡⟨ cong
                       (_, fromFin (toFin y))
                       (Inverse.left-inverse-of (IsFinite.iso finA) x) ⟩
                    x , fromFin (toFin y)

                  ≡⟨ cong (x ,_)
                       (Inverse.left-inverse-of (IsFinite.iso finB) y) ⟩
                    x , y
                  ∎
            ; right-inverse-of = λ xy →
                let x , y = Fin.remQuot ∥ B ∥ xy in
                begin
                  Fin.combine (toFin (fromFin {A} x)) (toFin (fromFin {B} y))
                ≡⟨ cong
                     (λ x → Fin.combine x (toFin (fromFin {B} y)))
                     (Inverse.right-inverse-of (IsFinite.iso finA) x) ⟩
                  Fin.combine x (toFin (fromFin {B} y))
                ≡⟨ cong
                     (Fin.combine x)
                     (Inverse.right-inverse-of (IsFinite.iso finB) y) ⟩
                  Fin.combine x y
                ≡⟨⟩
                  uncurry Fin.combine (Fin.remQuot {∥ A ∥} ∥ B ∥ xy)
                ≡⟨ combine-remQuot {∥ A ∥} ∥ B ∥ xy ⟩
                  xy
                ∎
            }
        }
    }
   where
    open ≡-Reasoning

record FinSet : Set₁ where
  field
    A : Set
    fin : IsFinite A
