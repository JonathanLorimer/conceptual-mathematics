
module Session5.Section3 where

open import Categories
open import Category.SET
open import SectionsAndRetractions SET

open Category SET

data One : Set where
  one : One

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

ex1 : ∀ {A B C} {h : A → C} {g : B → C} {f : A → B} → (h ≈ g ∘ f) → (a1 a2 : One → A) → f ∘ a1 ≈ f ∘ a2 → h ∘ a1 ≈ h ∘ a2
ex1 {h = h} {g} {f} hgfeq a1 a2 feq x =
  begin
    (h ∘ a1) x
  ≡⟨ hgfeq (a1 x) ⟩
    ((g ∘ f) ∘ a1) x
  ≡⟨⟩
    (g ∘ (f ∘ a1)) x
  ≡⟨ cong g (feq x) ⟩
    (g ∘ (f ∘ a2)) x
  ≡⟨⟩
    ((g ∘ f) ∘ a2) x
  ≡⟨ sym (hgfeq (a2 x)) ⟩
    (h ∘ a2) x
  ∎

open import Data.Product

ex2-a : ∀ {A B C} {h : A → C} {g : B → C} {f : A → B} → (h ≈ g ∘ f) → (a : A) → Σ B (\b → h a ≡ g b)
proj₁ (ex2-a {h = h} {g} {f} hgfeq a) = f a
proj₂ (ex2-a {h = h} {g} {f} hgfeq a) rewrite hgfeq a = refl

data Void : Set where

const : {A B : Set} → A → B → A
const a _ = a

data Bool : Set where
  true : Bool
  false : Bool

-- Intuition: no! Not if g is const.
ex2-b : (∀ {A B C} {h : A → C} {g : B → C} → (a : A) → Σ B (\b → h a ≡ g b) → Σ (A → B) (\f → h ≈ g ∘ f)) → Void
ex2-b hyp with hyp {h = id} {g = const true} true (true , refl)
... | _ , snd with snd false
...           | ()


