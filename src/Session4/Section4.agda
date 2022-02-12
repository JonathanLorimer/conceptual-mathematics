module Session4.Section4 where

open import Categories
open import Category.MON
open Category MON

open import Algebra.Bundles using (Monoid)
open Monoid

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Data.Nat
open import Data.Nat.Properties

-- these truly need to be reals, or at least rationals! Nats dont have the inverses we need!

natPlus : Obj
Carrier natPlus = _
_≈_ natPlus = _
_∙_ natPlus = _
ε natPlus = _
isMonoid natPlus = +-0-isMonoid

natTimes : Obj
Carrier natTimes = _
_≈_ natTimes = _
_∙_ natTimes = _
ε natTimes = _
isMonoid natTimes = *-1-isMonoid

open import Data.Nat.Solver
open +-*-Solver

d : natPlus ~> natPlus
MonArr.map d x = 2 * x
MonArr.commutes d = solve 2 (\a b → a :+ b :+ (a :+ b :+ con 0) := a :+ (a :+ con 0) :+ (b :+ (b :+ con 0))) Eq.refl
MonArr.preserves-≈ d a a' eq rewrite eq = Eq.refl

c : natTimes ~> natTimes
MonArr.map c x = x ^ 3
MonArr.commutes c =
  solve 2 (\a b → (a :* b) :* ((a :* b) :* ((a :* b) :* con 1)) := a :* (a :* (a :* con 1)) :* (b :* (b :* (b :* con 1)))) Eq.refl
MonArr.preserves-≈ c a b eq rewrite eq = Eq.refl

