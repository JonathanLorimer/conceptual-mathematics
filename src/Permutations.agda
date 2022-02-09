{-# OPTIONS --type-in-type #-}
module Permutations where

open import Function hiding (id)
open import Data.Empty
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Function.Reasoning
open import Isomorphisms

record Category : Set where
  infix 6 _~>_
  field
    Obj : Set
    _~>_ : (A B : Obj) → Set

    id : {A : Obj} → A ~> A
    _>>_ : {A B C : Obj} → A ~> B → B ~> C → A ~> C

    id-l : {A B : Obj} (f : A ~> B) → id >> f ≡ f
    id-r : {A B : Obj} (f : A ~> B) → f >> id ≡ f
    >>-assoc : {A B C D : Obj} (f : A ~> B) → (g : B ~> C) → (h : C ~> D) → f >> (g >> h) ≡ (f >> g) >> h


infix 5 _[_,_]
_[_,_] : (C : Category) -> Category.Obj C -> Category.Obj C -> Set
C [ X , Y ] = Category._~>_ C X Y

infix 5 _[_>>_]
_[_>>_] : (C : Category) -> {X Y Z : Category.Obj C} -> C [ X , Y ] -> C [ Y , Z ] -> C [ X , Z ]
C [ f >> g ] = Category._>>_ C f g


SET : Category
SET = record
        { Obj = Set
        ; _~>_ = \ S T → S → T
        ; id = \ x → x
        ; _>>_ = λ f g x →  g (f x)
        ; id-l = \f -> refl
        ; id-r = \f -> refl
        ; >>-assoc = \f g h -> refl
        }

-- f ∘ α ≡ β ∘ f
open Category

record PermObj : Set where
  field
    permCarrier : Set
    permAuto : Automorphism permCarrier

open Isomorphism
open PermObj

record PermArrow ( A B : PermObj ) : Set where
  field
    ⟳_ : permCarrier A -> permCarrier B
    permArrowLaw : (x : permCarrier A) -> (⟳_ ∘ forward (permAuto A)) x ≡ (forward (permAuto B) ∘ ⟳_) x

open PermArrow

PERM : Category
Category.Obj PERM = PermObj
Category._~>_ PERM = PermArrow
⟳ (Category.id PERM) = SET .id
permArrowLaw (Category.id PERM) x = refl
(_>>_ PERM  {A = A} {B = B} {C = C}
  record { ⟳_ = f⟳ ; permArrowLaw = flaw })
  record { ⟳_ = g⟳ ; permArrowLaw = glaw } =
  record { ⟳_ = g⟳ ∘ f⟳
         ; permArrowLaw = λ x →
            begin
            (g⟳ ∘ f⟳ ∘ forward (permAuto A)) x
            ≡⟨ cong g⟳  (flaw x)⟩
            (g⟳ ∘ (forward (permAuto B)) ∘ f⟳) x
            ≡⟨ glaw (f⟳ x) ⟩
            (forward (permAuto C) ∘ g⟳ ∘ f⟳) x
            ∎
         }
Category.id-l PERM = ?
Category.id-r PERM = ?
Category.>>-assoc PERM = ?

