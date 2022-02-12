module Session4.Section4 where

open import Categories
open import Category.MON
open Category MON

open import Algebra.Bundles using (Monoid)
open import Algebra.Structures
open Monoid

open import Relation.Binary.Structures
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

module _ where

  open import Data.Rational
  open import Data.Integer using (0ℤ; 1ℤ; +_)
  open import Data.Rational.Properties


  ratPlus : Obj
  Carrier ratPlus = _
  _≈_ ratPlus = _
  _∙_ ratPlus = _
  ε ratPlus = _
  isMonoid ratPlus = +-0-isMonoid

  ratTimes : Obj
  Carrier ratTimes = _
  _≈_ ratTimes = _
  _∙_ ratTimes = _
  ε ratTimes = _
  isMonoid ratTimes = *-1-isMonoid

  open import Data.Rational.Solver
  open +-*-Solver

  d : ratPlus ~> ratPlus
  MonArr.map d x = x + x
  MonArr.commutes d = solve 2 (\a b → (a :+ b) :+ (a :+ b) := (a :+ a) :+ (b :+ b)) Eq.refl
  MonArr.preserves-≈ d a a' eq rewrite eq = Eq.refl

  open import Isomorphisms MON
  open Isomorphism

  half : ℚ
  half = normalize 1 2

  h : ratPlus ~> ratPlus
  MonArr.map h x = x * half
  MonArr.commutes h = solve 2 (\a b → (a :+ b) :* con half := (a :* con half) :+ (b :* con half)) Eq.refl
  MonArr.preserves-≈ h a b eq rewrite eq = Eq.refl

  ex1 : Isomorphism ratPlus ratPlus
  forward ex1 = d
  backward ex1 = h
  fInverse ex1 = solve 1 (\a → a :* con half :+ a :* con half := a) Eq.refl
  bInverse ex1 = solve 1 (\a → (a :+ a) :* con half := a) Eq.refl


module _ where

  data Oddity : Set where
    even : Oddity
    odd : Oddity

  _o+_ : Oddity → Oddity → Oddity
  even o+ a = a
  odd o+ even = odd
  odd o+ odd = even

  data Signedness : Set where
    positive : Signedness
    negative : Signedness

  _s*_ : Signedness → Signedness → Signedness
  positive s* b = b
  negative s* positive = negative
  negative s* negative = positive

  open IsMonoid
  open import Data.Product

  odd+ : Obj
  Carrier odd+ = Oddity
  _≈_ odd+ = _≡_
  _∙_ odd+ = _o+_
  ε odd+ = even
  IsEquivalence.refl (IsMagma.isEquivalence (IsSemigroup.isMagma (isSemigroup (isMonoid odd+)))) = Eq.refl
  IsEquivalence.sym (IsMagma.isEquivalence (IsSemigroup.isMagma (isSemigroup (isMonoid odd+)))) = Eq.sym
  IsEquivalence.trans (IsMagma.isEquivalence (IsSemigroup.isMagma (isSemigroup (isMonoid odd+)))) = Eq.trans
  IsMagma.∙-cong (IsSemigroup.isMagma (isSemigroup (isMonoid odd+))) eq1 eq2 rewrite eq1 | eq2 = Eq.refl
  IsSemigroup.assoc (isSemigroup (isMonoid odd+)) = λ { even even even → Eq.refl
                                                      ; even even odd → Eq.refl
                                                      ; even odd even → Eq.refl
                                                      ; even odd odd → Eq.refl
                                                      ; odd even even → Eq.refl
                                                      ; odd even odd → Eq.refl
                                                      ; odd odd even → Eq.refl
                                                      ; odd odd odd → Eq.refl
                                                      }
  proj₁ (identity (isMonoid odd+)) x = Eq.refl
  proj₂ (identity (isMonoid odd+)) even = Eq.refl
  proj₂ (identity (isMonoid odd+)) odd = Eq.refl

  sign* : Obj
  Carrier sign* = Signedness
  _≈_ sign* = _≡_
  _∙_ sign* = _s*_
  ε sign* = positive
  IsEquivalence.refl (IsMagma.isEquivalence (IsSemigroup.isMagma (isSemigroup (isMonoid sign*)))) = Eq.refl
  IsEquivalence.sym (IsMagma.isEquivalence (IsSemigroup.isMagma (isSemigroup (isMonoid sign*)))) = Eq.sym
  IsEquivalence.trans (IsMagma.isEquivalence (IsSemigroup.isMagma (isSemigroup (isMonoid sign*)))) = Eq.trans
  IsMagma.∙-cong (IsSemigroup.isMagma (isSemigroup (isMonoid sign*))) eq1 eq2 rewrite eq1 | eq2 = Eq.refl
  IsSemigroup.assoc (isSemigroup (isMonoid sign*)) = λ { positive positive positive → Eq.refl
                                                       ; positive positive negative → Eq.refl
                                                       ; positive negative positive → Eq.refl
                                                       ; positive negative negative → Eq.refl
                                                       ; negative positive positive → Eq.refl
                                                       ; negative positive negative → Eq.refl
                                                       ; negative negative positive → Eq.refl
                                                       ; negative negative negative → Eq.refl
                                                       }
  proj₁ (identity (isMonoid sign*)) x = Eq.refl
  proj₂ (identity (isMonoid sign*)) positive = Eq.refl
  proj₂ (identity (isMonoid sign*)) negative = Eq.refl

  open import Isomorphisms MON
  open Isomorphism

  ex2 : Isomorphism odd+ sign*
  MonArr.map (forward ex2) even = positive
  MonArr.map (forward ex2) odd = negative
  MonArr.commutes (forward ex2) even even = Eq.refl
  MonArr.commutes (forward ex2) even odd = Eq.refl
  MonArr.commutes (forward ex2) odd even = Eq.refl
  MonArr.commutes (forward ex2) odd odd = Eq.refl
  MonArr.preserves-≈ (forward ex2) even even x = Eq.refl
  MonArr.preserves-≈ (forward ex2) odd odd x = Eq.refl
  MonArr.map (backward ex2) positive = even
  MonArr.map (backward ex2) negative = odd
  MonArr.commutes (backward ex2) positive positive = Eq.refl
  MonArr.commutes (backward ex2) positive negative = Eq.refl
  MonArr.commutes (backward ex2) negative positive = Eq.refl
  MonArr.commutes (backward ex2) negative negative = Eq.refl
  MonArr.preserves-≈ (backward ex2) positive positive x = Eq.refl
  MonArr.preserves-≈ (backward ex2) negative negative x = Eq.refl
  fInverse ex2 positive = Eq.refl
  fInverse ex2 negative = Eq.refl
  bInverse ex2 even = Eq.refl
  bInverse ex2 odd = Eq.refl

