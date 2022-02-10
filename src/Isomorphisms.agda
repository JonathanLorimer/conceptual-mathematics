open import Categories

module Isomorphisms (C : Category) where

import Relation.Binary.PropositionalEquality as Eq
open import Function using (_$_)

open Category C
open HomReasoning

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
fInverse (transitiveIso fiso giso) =
  begin
    forward (transitiveIso fiso giso) ∘ backward (transitiveIso fiso giso)
  ≡⟨⟩
    (forward giso ∘ forward fiso) ∘ backward (transitiveIso fiso giso)
  ≡⟨⟩
    (forward giso ∘ forward fiso) ∘ (backward fiso ∘ backward giso)
  ≈⟨ sym $ ∘-assoc _ _ _ ⟩
    forward giso ∘ (forward fiso ∘ (backward fiso ∘ backward giso))
  ≈⟨ ∘-cong refl $ ∘-assoc _ _ _ ⟩
    forward giso ∘ ((forward fiso ∘ backward fiso) ∘ backward giso)
  ≈⟨ ∘-cong refl $ ∘-cong (fInverse fiso) refl ⟩
    forward giso ∘ (id ∘ backward giso)
  ≈⟨ ∘-cong refl (id-l $ backward giso) ⟩
    forward giso ∘ backward giso
  ≈⟨ fInverse giso ⟩
    id
  ∎
bInverse (transitiveIso fiso giso) =
  begin
    backward (transitiveIso fiso giso) ∘ forward (transitiveIso fiso giso)
  ≡⟨⟩
    (backward fiso ∘ backward giso) ∘ (forward giso ∘ forward fiso)
  ≈⟨ sym $ ∘-assoc _ _ _ ⟩
    backward fiso ∘ (backward giso ∘ (forward giso ∘ forward fiso))
  ≈⟨ ∘-cong refl $ ∘-assoc _ _ _ ⟩
    backward fiso ∘ ((backward giso ∘ forward giso) ∘ forward fiso)
  ≈⟨ ∘-cong refl $ ∘-cong (bInverse giso) refl ⟩
    backward fiso ∘ (id ∘ forward fiso)
  ≈⟨ ∘-cong refl (id-l $ forward fiso) ⟩
    backward fiso ∘ forward fiso
  ≈⟨ bInverse fiso ⟩
    id
  ∎


Automorphism : Obj -> Set
Automorphism A = Isomorphism A A

