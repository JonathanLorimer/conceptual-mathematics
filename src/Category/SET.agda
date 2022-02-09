{-# OPTIONS --type-in-type #-}

module Category.SET where

open import Categories
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)


postulate
  extensionality : {S : Set}{T : S -> Set}
                   {f g : (x : S) -> T x} ->
                   ((x : S) -> f x ≡ g x) ->
                   f ≡ g

open Category

SET : Category
Obj     SET        = Set
_~>_    SET S T    = S → T
-- _≈_     SET {A} f g = forall (a : A) → f a ≡ g a
-- ≈-refl  (≈-equiv SET) _     = refl
-- ≈-sym   (≈-equiv SET) p a   = Eq.sym (p a)
-- ≈-trans (≈-equiv SET) x y a = Eq.trans (x a) (y a)
id      SET        = \a → a
_∘_     SET        = \g f a → g (f a)
id-r    SET _      = refl
id-l    SET _      = refl
∘-assoc SET _  _ _ = refl

