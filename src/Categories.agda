{-# OPTIONS --type-in-type #-}

module Categories where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

-- open import Relation.Binary.Structures using (IsEquivalence)
-- open import Relation.Binary.Bundles using (Setoid)

infix 2 _≈_
_≈_ = _≡_

record Category : Set where
  infix 6 _~>_

  field
    -- Objects and arrows in the category
    Obj : Set
    _~>_ : (A B : Obj) → Set

    -- One day soon we will want to loosen the meaning of equality. But that
    -- day is not this day and I don't know how to do this ergonomically.

    -- -- The meaning of equality of morphisms
    -- _≈_ : {A B : Obj} → A ~> B → A ~> B → Set

    -- -- _≈_ forms a equivalence relationship
    -- ≈-equiv : {A B : Obj} → IsEquivalence (_≈_ {A} {B})

    -- Id and composition
    id : {A : Obj} → A ~> A
    _∘_ : {A B C : Obj} → B ~> C → A ~> B → A ~> C

    -- Laws
    id-r : {A B : Obj} (f : A ~> B) → f ∘ id ≈ f
    id-l : {A B : Obj} (f : A ~> B) → id ∘ f ≈ f
    ∘-assoc : {A B C D : Obj} (f : A ~> B) → (g : B ~> C) → (h : C ~> D) → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f

  -- "Forward" composition
  _>>_ : {A B C : Obj} → A ~> B → B ~> C → A ~> C
  _>>_ f g = g ∘ f

  -- setoid : {X Y : Obj} → Setoid _ _
  -- Setoid.Carrier (setoid {X} {Y}) = X ~> Y
  -- Setoid._≈_ setoid  = _≈_
  -- Setoid.isEquivalence setoid = ≈-equiv

open Category


-- Notational convenience for arrows in a category. Helpful when dealing with
-- multiple categories at once.
-- eg we can talk about a set arrow via `SET [ Bool , Int ]`
infix 5 _[_,_]
_[_,_] : (C : Category) -> Obj C -> Obj C -> Set
C [ X , Y ] = _~>_ C X Y

-- Notational convenience for composition.
-- eg we can talk about a set composition `SET [ show ∘ length ] : SET [ List A , String ]`
infix 5 _[_∘_]
_[_∘_] : (C : Category) -> {X Y Z : Obj C} -> C [ Y , Z ] -> C [ X , Y ] -> C [ X , Z ]
_[_∘_] = _∘_

-- Same, but for double composition
infix 5 _[_∘_∘_]
_[_∘_∘_] : (C : Category) -> {X Y Z W : Obj C} -> C [ Z , W ] → C [ Y , Z ] -> C [ X , Y ] -> C [ X , W ]
C [ h ∘ g ∘ f ] = C [ h ∘ C [ g ∘ f ] ]

-- Notational convenience for "forward" composition.
-- eg we can talk about a set composition `SET [ length >> show ] : SET [ List A , String ]`
infix 5 _[_>>_]
_[_>>_] : (C : Category) -> {X Y Z : Obj C} -> C [ X , Y ] -> C [ Y , Z ] -> C [ X , Z ]
_[_>>_] = _>>_

-- Same, but for double
infix 5 _[_>>_>>_]
_[_>>_>>_] : (C : Category) -> {X Y Z W : Obj C} -> C [ X , Y ] -> C [ Y , Z ] -> C [ Z , W ] → C [ X , W ]
C [ f >> g >> h ] = C [ f >> C [ g >> h ] ]

