{-# OPTIONS --type-in-type #-}

module Category.MON where

open import Algebra.Bundles using (Monoid)
open import Categories
open import Relation.Binary.Bundles

open import Relation.Binary.Structures

import Relation.Binary.Reasoning.Setoid as SetoidR

record MonArr (S T : Monoid _ _) : Set where
  open Monoid S using (_∙_) renaming (_≈_ to _≋_)
  open Monoid T using (_≈_) renaming (_∙_ to _×_)
  field
    map : Monoid.Carrier S → Monoid.Carrier T
    commutes
      : (a b : Monoid.Carrier S)
      → map (a ∙ b) ≈ map a × map b
    preserves-≈
      : (a a' : Monoid.Carrier S)
      → a ≋ a'
      → map a ≈ map a'

open Category hiding (setoid)
open MonArr
open Monoid hiding (_∙_)

MON : Category
Obj     MON = Monoid _ _
_~>_    MON = MonArr
_≈_     MON {A = A} {B = B} f g = forall (a : Carrier A) → B ._≈_ (map f a) (map g a)
IsEquivalence.refl (≈-equiv MON {B = B}) a = B .refl
IsEquivalence.sym (≈-equiv MON {B = B}) f a = B .sym (f a)
IsEquivalence.trans (≈-equiv MON {B = B}) f g a = B .trans (f a) (g a)
map (id MON) a = a
commutes (id MON {A = A}) a b = A .refl
preserves-≈ (id MON {A = A}) a a' eq = eq
map ((MON ∘ g) f) a = map g (map f a)
commutes (_∘_ MON {A = A} {B} {C} g f) a a' =
  begin
    map g (map f (a × a'))
  ≈⟨ preserves-≈ g _ _ (commutes f a a') ⟩
    map g (map f a ⊗ map f a')
  ≈⟨ commutes g _ _ ⟩
    map g (map f a) ∙ map g (map f a')
  ∎
  where
    open SetoidR (setoid C) public
    open Monoid A using () renaming (_∙_ to _×_)
    open Monoid B using () renaming (_∙_ to _⊗_)
    open Monoid C
preserves-≈ (_∘_ MON g f) a a' eq =
  g .preserves-≈ _ _ (f .preserves-≈ _ _ eq)
∘-cong MON {A = A} {B} {C} {g} {g'} {f} {f'} geq feq a =
  begin
    map g (map f a)
  ≈⟨ g .preserves-≈ _ _ (feq _) ⟩
    map g (map f' a)
  ≈⟨ geq _ ⟩
    map g' (map f' a)
  ∎
  where
    open SetoidR (setoid C) public
id-r    MON {B = B} f a = B .refl
id-l    MON {B = B} f a = B .refl
∘-assoc MON {D = D} h g f a = D .refl

