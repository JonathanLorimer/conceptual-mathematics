{-# OPTIONS --type-in-type #-}

module Category.MON where

open import Algebra.Bundles using (Monoid)
open import Categories
open import Relation.Binary.Bundles

open import Relation.Binary.Structures

record MonArr (S T : Monoid _ _) : Set where
  open Monoid S using (_∙_)
  open Monoid T using (_≈_) renaming (_∙_ to _×_)
  field
    map : Monoid.Carrier S → Monoid.Carrier T
    commutes
      : (a b : Monoid.Carrier S)
      → map (a ∙ b) ≈ map a × map b

open Category hiding (setoid)
open MonArr
open Monoid

MON : Category
Obj     MON = Monoid _ _
_~>_    MON = MonArr
_≈_     MON {A = A} {B = B} f g = forall (a : Carrier A) → B ._≈_ (map f a) (map g a)
IsEquivalence.refl (≈-equiv MON {B = B}) = IsEquivalence.refl (Setoid.isEquivalence (B .setoid))
IsEquivalence.sym (≈-equiv MON {B = B}) = ?
IsEquivalence.trans (≈-equiv MON {B = B}) = ?
id      MON = ?
_∘_     MON = ?
∘-cong  MON = ?
id-r    MON = ?
id-l    MON = ?
∘-assoc MON = ?
