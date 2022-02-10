{-# OPTIONS --type-in-type #-}

module Category.PERM where

open import Categories
open Category
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Binary.Structures

import Isomorphisms
open Isomorphisms.Isomorphism
open import Category.SET
open Category SET using () renaming (_∘_ to _⊚_; ∘-assoc to ⊚-assoc)
open HomReasoning SET

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
      : SET [ SET [ permMap ∘ forward (permAuto A) ]
            ≈ SET [ forward (permAuto B) ∘ permMap ]
            ]

open PermArrow


PERM : Category
Obj     PERM = PermObj
_~>_    PERM = PermArrow
_≈_     PERM A B = SET [ permMap A ≈ permMap B ]
≈-equiv PERM = record
  { refl  = SET .≈-equiv .IsEquivalence.refl
  ; sym   = SET .≈-equiv .IsEquivalence.sym
  ; trans = SET .≈-equiv .IsEquivalence.trans
  }
permMap      (id PERM) = id SET
permArrowLaw (id PERM) a = Eq.refl
permMap      ((PERM ∘ g) f) = SET [ permMap g ∘ permMap f ]
permArrowLaw (_∘_ PERM {A} {B} {C}
  record { permMap = gmap ; permArrowLaw = glaw }
  record { permMap = fmap ; permArrowLaw = flaw }) =
  begin
    (gmap ⊚ fmap) ⊚ forward (permAuto A)    ≈⟨ ⊚-assoc _ fmap gmap ⟩
                                            -- how do i cong?
    gmap ⊚ (fmap ⊚ forward (permAuto A))    ≈⟨ ? ⟩
    gmap ⊚ (forward (permAuto B) ⊚ fmap)    ≈⟨ ⊚-assoc fmap (forward (permAuto B)) gmap ⟩
    (gmap ⊚ forward (permAuto B) ) ⊚ fmap   ≈⟨ ? ⟩
    forward (permAuto C) ⊚ (gmap ⊚ fmap)
  ∎
id-r    PERM f a = Eq.refl
id-l    PERM f a = Eq.refl
∘-assoc PERM f g h a = Eq.refl

