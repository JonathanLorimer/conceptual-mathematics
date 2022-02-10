{-# OPTIONS --type-in-type #-}

module Category.PERM where

open import Categories
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym; trans)
open import Relation.Binary.Structures
open import Category.SET
import Isomorphisms
open import Isomorphisms SET

open Isomorphisms.Isomorphism
open Category
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)



record PermObj : Set where
  field
    carrier : Set
    auto : Automorphism carrier

open Isomorphism
open PermObj

record PermArrow ( A B : PermObj ) : Set where
  field
    map : carrier A → carrier B
    map-commutes
      : (a : carrier A)
      → map (forward (auto A) a) ≡ forward (auto B) (map a)

open PermArrow


PERM : Category
Obj     PERM = PermObj
_~>_    PERM = PermArrow
_≈_     PERM f g = forall a → map f a ≡ map g a
IsEquivalence.refl  (≈-equiv PERM) _     = refl
IsEquivalence.sym   (≈-equiv PERM) f a   = Eq.sym (f a)
IsEquivalence.trans (≈-equiv PERM) f g a = Eq.trans (f a) (g a)
map      (id PERM) = id SET
map-commutes (id PERM) a = refl
map      ((PERM ∘ g) f) a = map g (map f a)
map-commutes (_∘_ PERM {A} {B} {C}
  g@record { map = gmap ; map-commutes = glaw }
  f@record { map = fmap ; map-commutes = flaw }) a =
  let perm t = forward (auto t)
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
        | gg' (map f' a)
        = refl
id-r    PERM f a = refl
id-l    PERM f a = refl
∘-assoc PERM f g h a = refl

