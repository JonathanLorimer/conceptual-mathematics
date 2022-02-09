{-# OPTIONS --allow-unsolved-metas #-}

open import Categories

module Isomorphisms (C : Category) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Category.SET
open import Function using (_$_)

open Category C

record Isomorphism (A B : Obj) : Set where
  field
    forward  : C [ A , B ]
    backward : C [ B , A ]
    fInverse : forward ∘ backward ≈ id
    bInverse : backward ∘ forward ≈ id

open Isomorphism

reflexiveIso : {A : Obj} → Isomorphism A A
forward reflexiveIso = id
backward reflexiveIso = id
fInverse reflexiveIso = id-l id
bInverse reflexiveIso = id-l id

symmetricIso : {A B : Obj}  → Isomorphism A B → Isomorphism B A
forward (symmetricIso iso)  = backward iso
backward (symmetricIso iso) = forward iso
fInverse (symmetricIso iso) = bInverse iso
bInverse (symmetricIso iso) = fInverse iso

transitiveIso
  : {X Y Z : Obj}
  → Isomorphism X Y
  → Isomorphism Y Z
  → Isomorphism X Z
forward  (transitiveIso fiso giso) = forward fiso >> forward giso
backward (transitiveIso fiso giso) = backward giso >> backward fiso
fInverse (transitiveIso fiso giso) = ?
bInverse (transitiveIso fiso giso) = ?


Automorphism : Obj -> Set
Automorphism A = Isomorphism A A

