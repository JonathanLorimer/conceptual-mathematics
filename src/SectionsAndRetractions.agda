open import Categories

module SectionsAndRetractions (C : Category) where

open Category C

record Determination {X Y Z : Obj} (h : X ~> Z) (f : X ~> Y) : Set where
  constructor determines
  field
    r : Y ~> Z
    commute : r ∘ f ≈ h

HasRetract : {A B : Obj} (f : A ~> B) -> Set
HasRetract = Determination id

record Choice {X Y Z : Obj} (h : X ~> Z) (g : Y ~> Z) : Set where
  constructor chooses
  field
    s : X ~> Y
    commute : g ∘ s ≈ h

HasSection : {A B : Obj} (f : A ~> B) -> Set
HasSection = Choice id

