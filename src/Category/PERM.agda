{-# OPTIONS --type-in-type #-}

module Category.PERM where

open import Categories
open Category
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Binary.Structures

import Isomorphisms
open Isomorphisms.Isomorphism
open import Category.SET

open import Isomorphisms SET


record PermObj : Set where
  field
    permCarrier : Set
    permAuto : Automorphism permCarrier

open Isomorphism
open PermObj

record PermArrow ( A B : PermObj ) : Set where
  field
    permMap : permCarrier A → permCarrier B
    permArrowLaw
      : (a : permCarrier A)
      → permMap (forward (permAuto A) a) ≡ forward (permAuto B) (permMap a)

open PermArrow


PERM : Category
Obj     PERM = PermObj
_~>_    PERM = PermArrow
_≈_     PERM f g = forall a → permMap f a ≡ permMap g a
IsEquivalence.refl  (≈-equiv PERM) _     = refl
IsEquivalence.sym   (≈-equiv PERM) f a   = Eq.sym (f a)
IsEquivalence.trans (≈-equiv PERM) f g a = Eq.trans (f a) (g a)
permMap      (id PERM) = id SET
permArrowLaw (id PERM) a = refl
permMap      ((PERM ∘ g) f) a = permMap g (permMap f a)
permArrowLaw (_∘_ PERM {A} {B} {C}
  g@record { permMap = gmap ; permArrowLaw = glaw }
  f@record { permMap = fmap ; permArrowLaw = flaw }) a =
  let perm t = forward (permAuto t)
  in
  begin
    gmap (fmap (perm A a))
  ≡⟨ cong gmap (flaw a) ⟩
    gmap (perm B (fmap a))
  ≡⟨ glaw (fmap a) ⟩
    perm C (gmap (fmap a))
  ∎
∘-cong  PERM {f' = f'} gg' ff' a
  rewrite ff' a
        | gg' (permMap f' a)
        = refl
id-r    PERM f a = refl
id-l    PERM f a = refl
∘-assoc PERM f g h a = refl

