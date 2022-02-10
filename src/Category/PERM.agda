{-# OPTIONS --type-in-type #-}

module Category.PERM where

open import Categories
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym; trans)
open import Relation.Binary.Structures
open import Category.SET
import Isomorphisms
open import Isomorphisms SET


module _ where

  open Isomorphisms.Isomorphism
  open Category
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

  record PermObj : Set where
    field
      carrier : Set
      auto : Automorphism carrier

  open Isomorphism
  open PermObj

  record PermArrow ( A B : PermObj ) : Set where
    field
      map : carrier A → carrier B
      map-commutes
        : (a : carrier A)
        → map (forward (auto A) a) ≡ forward (auto B) (map a)

  open PermArrow


  PERM : Category
  Obj     PERM = PermObj
  _~>_    PERM = PermArrow
  _≈_     PERM f g = forall a → map f a ≡ map g a
  IsEquivalence.refl  (≈-equiv PERM) _     = refl
  IsEquivalence.sym   (≈-equiv PERM) f a   = Eq.sym (f a)
  IsEquivalence.trans (≈-equiv PERM) f g a = Eq.trans (f a) (g a)
  map      (id PERM) = id SET
  map-commutes (id PERM) a = refl
  map      ((PERM ∘ g) f) a = map g (map f a)
  map-commutes (_∘_ PERM {A} {B} {C}
    g@record { map = gmap ; map-commutes = glaw }
    f@record { map = fmap ; map-commutes = flaw }) a =
    let perm t = forward (auto t)
    in
    begin
      gmap (fmap (perm A a))
    ≡⟨ cong gmap (flaw a) ⟩
      gmap (perm B (fmap a))
    ≡⟨ glaw (fmap a) ⟩
      perm C (gmap (fmap a))
    ∎
  ∘-cong  PERM {f' = f'} gg' ff' a
    rewrite ff' a
          | gg' (map f' a)
          = refl
  id-r    PERM f a = refl
  id-l    PERM f a = refl
  ∘-assoc PERM f g h a = refl


module Ex where
  open import SectionsAndRetractions PERM
  open Isomorphism
  open Category PERM
  open Choice
  open PermObj
  open PermArrow
  open Isomorphisms.Isomorphism



  data Bool : Set where
    true : Bool
    false : Bool

  data Three : Set where
    this : Three
    that : Three
    other : Three

  data Four : Set where
    fone : Four
    ftwo : Four
    fthree : Four
    ffour : Four

  four-shuf : Four → Four
  four-shuf fone = ftwo
  four-shuf ftwo = fone
  four-shuf fthree = ffour
  four-shuf ffour = fthree

  four-pairs : Obj
  carrier four-pairs = Four
  forward (auto four-pairs) = four-shuf
  backward (auto four-pairs) = four-shuf
  fInverse (auto four-pairs) fone = refl
  fInverse (auto four-pairs) ftwo = refl
  fInverse (auto four-pairs) fthree = refl
  fInverse (auto four-pairs) ffour = refl
  bInverse (auto four-pairs) fone = refl
  bInverse (auto four-pairs) ftwo = refl
  bInverse (auto four-pairs) fthree = refl
  bInverse (auto four-pairs) ffour = refl

  data One : Set where
    one : One

  shuffle-3 : Three → Three
  shuffle-3 this = that
  shuffle-3 that = this
  shuffle-3 other = other



  shuffle-3-auto : Automorphism Three
  forward shuffle-3-auto = shuffle-3
  backward shuffle-3-auto = shuffle-3
  fInverse shuffle-3-auto this = refl
  fInverse shuffle-3-auto that = refl
  fInverse shuffle-3-auto other = refl
  bInverse shuffle-3-auto this = refl
  bInverse shuffle-3-auto that = refl
  bInverse shuffle-3-auto other = refl

  shuffle-3-obj : Obj
  carrier shuffle-3-obj = _
  auto shuffle-3-obj = shuffle-3-auto

  not : Bool → Bool
  not true = false
  not false = true

  not-auto : Automorphism Bool
  forward not-auto = not
  backward not-auto = not
  fInverse not-auto true = refl
  fInverse not-auto false = refl
  bInverse not-auto true = refl
  bInverse not-auto false = refl

  not-obj : Obj
  carrier not-obj = Bool
  auto not-obj = not-auto

  two-to-three : not-obj ~> shuffle-3-obj
  map two-to-three true = this
  map two-to-three false = that
  map-commutes two-to-three true = refl
  map-commutes two-to-three false = refl

  four-to-bool : four-pairs ~> not-obj
  map four-to-bool fone = false
  map four-to-bool ftwo = true
  map four-to-bool fthree = false
  map four-to-bool ffour = true
  map-commutes four-to-bool fone = refl
  map-commutes four-to-bool ftwo = refl
  map-commutes four-to-bool fthree = refl
  map-commutes four-to-bool ffour = refl

  four-to-bool' : four-pairs ~> not-obj
  map four-to-bool' fone = true
  map four-to-bool' ftwo = false
  map four-to-bool' fthree = true
  map four-to-bool' ffour = false
  map-commutes four-to-bool' fone = refl
  map-commutes four-to-bool' ftwo = refl
  map-commutes four-to-bool' fthree = refl
  map-commutes four-to-bool' ffour = refl

  bool-to-four : not-obj ~> four-pairs
  map bool-to-four true = fone
  map bool-to-four false = ftwo
  map-commutes bool-to-four true = refl
  map-commutes bool-to-four false = refl

  open Choice

  zoo : HasSection four-to-bool
  map (s zoo) true = ffour
  map (s zoo) false = fthree
  map-commutes (s zoo) true = refl
  map-commutes (s zoo) false = refl
  commute zoo true = refl
  commute zoo false = refl

  open Determination
  b24r : HasRetract bool-to-four
  map (r b24r) fone = true
  map (r b24r) ftwo = false
  map (r b24r) fthree = true
  map (r b24r) ffour = false
  map-commutes (r b24r) fone = refl
  map-commutes (r b24r) ftwo = refl
  map-commutes (r b24r) fthree = refl
  map-commutes (r b24r) ffour = refl
  commute b24r true = refl
  commute b24r false = refl


  one-auto : Automorphism One
  one-auto = reflexiveIso

  one-obj : Obj
  carrier one-obj = One
  auto one-obj = one-auto

