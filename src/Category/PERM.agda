{-# OPTIONS --type-in-type #-}

module Category.PERM where

open import Categories
open Category
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

open import Category.SET

open import Isomorphisms SET


record PermObj : Set where
  field
    permCarrier : SET .Obj
    permAuto : Automorphism permCarrier

open Isomorphism
open PermObj

record PermArrow ( A B : PermObj ) : Set where
  field
    permMap : SET [ permCarrier A , permCarrier B ]
    permArrowLaw
      : SET [ permMap ∘ forward (permAuto A) ]
      ≈ SET [ forward (permAuto B) ∘ permMap ]

open PermArrow

PERM : Category
Obj     PERM = PermObj
_~>_    PERM = PermArrow
permMap      (id PERM) = id SET
permArrowLaw (id PERM) = refl
permMap      ((PERM ∘ g) f) = SET [ permMap g ∘ permMap f ]
permArrowLaw ((PERM ∘ g) f) = ?
id-r    PERM f = ?
id-l    PERM f = ?
∘-assoc PERM = ?

