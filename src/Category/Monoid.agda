{-# OPTIONS --type-in-type #-}

open import Algebra.Bundles using (Monoid)

module Category.Monoid {c l} (M : Monoid c l) where

open import Categories
open Category hiding (setoid)
open Monoid M renaming (_≈_ to _≈M≈_)
open import Relation.Binary.Bundles

data One : Set where
  one : One

open import Relation.Binary.Structures

-- A one element category, whose morphisms are monoidal elements that get
-- multiplied in.
monoidCategory : Category
Obj     monoidCategory = One
_~>_    monoidCategory _ _ = Carrier
_≈_     monoidCategory = _≈M≈_
≈-equiv monoidCategory = Setoid.isEquivalence setoid
id      monoidCategory = ε
_∘_     monoidCategory = _∙_
∘-cong  monoidCategory = ∙-cong
id-r    monoidCategory = identityʳ
id-l    monoidCategory = identityˡ
∘-assoc monoidCategory f g h = sym (assoc f g h)

