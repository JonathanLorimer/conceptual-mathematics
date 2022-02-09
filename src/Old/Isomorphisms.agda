module Old.Isomorphisms where

open import Function
open import Data.Empty
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Function.Reasoning

record Isomorphism (A B : Set) : Set where
  field
    forward : A → B
    backward : B → A
    fInverse : (x : B) -> (forward ∘ backward) x ≡ id x
    bInverse : (x : A) -> (backward ∘ forward) x ≡ id x

data SetB : Set where
  Feather : SetB
  Stone : SetB
  Flower : SetB

data SetA : Set where
  Mother : SetA
  Father : SetA
  Child : SetA

abIso : Isomorphism SetA SetB
Isomorphism.forward abIso Mother = Feather
Isomorphism.forward abIso Father = Stone
Isomorphism.forward abIso Child = Flower
Isomorphism.backward abIso Feather = Mother
Isomorphism.backward abIso Stone = Father
Isomorphism.backward abIso Flower = Child
Isomorphism.fInverse abIso Feather = refl
Isomorphism.fInverse abIso Stone = refl
Isomorphism.fInverse abIso Flower = refl
Isomorphism.bInverse abIso Mother = refl
Isomorphism.bInverse abIso Father = refl
Isomorphism.bInverse abIso Child = refl

reflexiveIso : {A : Set} -> Isomorphism A A
reflexiveIso = record
                 { forward = λ z → z
                 ; backward = λ z → z
                 ; fInverse = λ x → refl
                 ; bInverse = λ x → refl
                 }

symmetricIso : {A B : Set } -> Isomorphism A B -> Isomorphism B A
symmetricIso record { forward = f ; backward = g ; fInverse = fInverse ; bInverse = gInverse } =
  record
    { forward = g
    ; backward = f
    ; fInverse = gInverse
    ; bInverse = fInverse
    }

transitiveIso : {A B C : Set } -> Isomorphism A B -> Isomorphism B C -> Isomorphism A C
transitiveIso
  record { forward = f₁ ; backward = g₁ ; fInverse = fInverse₁ ; bInverse = gInverse₁ }
  record { forward = f ; backward = g ; fInverse = fInverse ; bInverse = gInverse } =
    record
      { forward = λ z → f (f₁ z)
      ; backward = λ z → g₁ (g z)
      ; fInverse = λ x →
            begin
            f (f₁ (g₁ (g x)))
            ≡⟨ cong f $ fInverse₁ (g x) ⟩
            f (id (g x))
            ≡⟨⟩
            f (g x)
            ≡⟨ fInverse x ⟩
            id x
            ∎
      ; bInverse = λ x →
            begin
            g₁ (g (f (f₁ x)))
            ≡⟨ cong g₁ $ gInverse (f₁ x) ⟩
            g₁ (id (f₁ x))
            ≡⟨ gInverse₁ x ⟩
            id x
            ∎
      }

open Isomorphism

uniqInv : { A B : Set } ->
  (gIso : Isomorphism A B) -> (kIso : Isomorphism A B) ->
  ((a : A ) -> (gIso .forward a ≡ kIso .forward a)) ->
  (x : B) ->
  gIso .backward x ≡ kIso .backward x
uniqInv
  record { forward = f₁ ; backward = g₁ ; fInverse = fInverse₁ ; bInverse = gInverse₁ } -- gIso
  record { forward = f ; backward = g ; fInverse = fInverse ; bInverse = gInverse } -- kIso
  fEq x =
    let feq = fEq (g₁ x)
        i1 = gInverse (g₁ x)
    in
        begin
        g₁ x
        ≡⟨ sym i1 ⟩
        g (f (g₁ x))
        ≡⟨ cong g (sym feq) ⟩
        g (f₁ (g₁ x))
        ≡⟨ cong g (fInverse₁ x) ⟩
        g x
        ∎

leftIsoCancellation : {A B : Set} ->
  (iso : Isomorphism A B) ->
  (h : B -> A) ->
  (k : B -> A) ->
  ((x : B) -> (iso .forward ∘ h) x ≡ (iso .forward ∘ k) x) ->
  (x : B) -> h x ≡ k x
leftIsoCancellation record { forward = f ; backward = g ; fInverse = fInverse ; bInverse = gInverse } h k isoEq x =
  begin
  h x
  ≡⟨ sym (gInverse (h x)) ⟩
  g (f (h x))
  ≡⟨ cong g (isoEq x) ⟩
  g (f (k x))
  ≡⟨ gInverse (k x) ⟩
  k x
  ∎

rightIsoCancellation : {A B : Set} ->
  (iso : Isomorphism A B) ->
  (h : B -> A) ->
  (k : B -> A) ->
  ((x : A) -> (h ∘ iso .forward) x ≡ (k ∘ iso .forward) x) ->
  (x : B) -> h x ≡ k x
rightIsoCancellation record { forward = f ; backward = g ; fInverse = fInverse ; bInverse = bInverse } h k isoEq x =
  begin
  h x
  ≡⟨ cong h (sym (fInverse x)) ⟩
  h (f (g x))
  ≡⟨ isoEq (g x) ⟩
  k (f (g x))
  ≡⟨ cong k (fInverse x) ⟩
  k x
  ∎

open import Data.Bool

counterExample : Isomorphism Bool Bool
counterExample =
    record
      { forward = not
      ; backward = not
      ; fInverse = λ { false → refl ; true -> refl }
      ; bInverse = λ { false → refl ; true -> refl }
      }

invalidIsoCancellation :
  (∀ {A h k a} -> (iso : Isomorphism A A)
             -> (h ∘ (forward iso)) a ≡ ((forward iso) ∘ k) a -> h a ≡ k a
  ) -> ⊥
invalidIsoCancellation eq
  with (eq {Bool} {const true} {const false} {true} counterExample refl)
... | ()


record Determination {A B C : Set} (h : A -> C) (f : A -> B) : Set where
  constructor determines
  field
    r : B -> C
    determinationProof : (a : A) ->  (r ∘ f) a ≡ h a

HasRetract : {A B : Set} (f : A -> B) -> Set
HasRetract = Determination id

record Choice {A B C : Set} (h : A -> C) (g : B -> C) : Set where
  constructor chooses
  field
    s : A -> B
    choiceProof : (a : A) -> (g ∘ s) a ≡ h a

HasSection : {A B : Set} (f : A -> B) -> Set
HasSection = Choice id

choiceForEverySection :
  {A B : Set} -> {f : A -> B} ->
  HasSection f ->
  ∀ {T : Set} -> (y : T -> B) -> Σ (T -> A) (λ (x : T -> A) -> (t : T) -> (f ∘ x) t ≡ y t)
choiceForEverySection {f = f} section {T} y =
  let open Choice section
      sec = s
      secEq = choiceProof
  in s ∘ y , \a ->
        begin
        (f ∘ (s ∘ y)) a
        ≡⟨⟩
        ((f ∘ s) ∘ y) a
        ≡⟨ secEq (y a) ⟩
        y a
        ∎

determinationForEveryRetraction :
  {A B : Set} -> {f : A -> B} ->
  HasRetract f ->
  ∀ {T : Set} -> (y : A -> T) -> Σ (B -> T) (λ (x : B -> T) -> (t : A) -> (x ∘ f) t ≡ y t)
determinationForEveryRetraction {f = f} ret {T} y =
  let open Determination ret
      r' = r
      retEq = determinationProof
  in y ∘ r , \a ->
       begin
       ( (y ∘ r) ∘ f ) a
       ≡⟨⟩
       ( y ∘ (r ∘ f) ) a
       ≡⟨ cong y (retEq a)  ⟩
       y a
       ∎

monomorphicChoice :
  {A B : Set} {f : A -> B} {T : Set} {x1 x2 : T -> A} ->
  HasRetract f ->
  (t : T) ->
  (f ∘ x1) t ≡ (f ∘ x2) t
  -> x1 t ≡ x2 t
monomorphicChoice {f = f} {x1 = x1} {x2 = x2} retF t eq =
  let open Determination retF
      r = r
      retEq = determinationProof
  in
  begin
  x1 t
  ≡⟨ sym $ retEq (x1 t) ⟩
  ((r ∘ f) ∘ x1) t
  ≡⟨ cong r eq ⟩
  ((r ∘ f) ∘ x2) t
  ≡⟨ retEq (x2 t) ⟩
  x2 t
  ∎

epimorphicDetermination :
  {A B : Set} {f : A -> B} {T : Set} -> {t1 t2 : B -> T} ->
  HasSection f ->
  ((a : A) -> (t1 ∘ f) a ≡ (t2 ∘ f) a) ->
  (b : B) ->
  t1 b ≡ t2 b
epimorphicDetermination {f = f} {t1 = t1} {t2 = t2} secF eq b =
  let open Choice secF
      s = s
      secEq = choiceProof
  in
  begin
  t1 b
  ≡⟨ sym $ cong t1 $ secEq b ⟩
  (t1 ∘ (f ∘ s)) b
  ≡⟨ eq (s b) ⟩
  ((t2 ∘ f) ∘ s) b
  ≡⟨ cong t2 $ secEq b ⟩
  t2 b
  ∎

retractionComposition :
  {A B C : Set} -> {f : A -> B} -> {g : B -> C} ->
  HasRetract f ->
  HasRetract g ->
  HasRetract (g ∘ f)
retractionComposition {f = f} record { r = r₁ ; determinationProof = retEq₁ } record { r = r ; determinationProof = retEq } =
  record
    { r = r₁ ∘ r
    ; determinationProof = \a -> trans (cong r₁ $ retEq (f a)) (retEq₁ a)
    }

record Idempotent {A : Set } (e : A -> A) : Set where
  field
    idempotentProof : e ∘ e ≡ e

idempotentSplit :
  {A B : Set} -> {s : A -> B} -> {r : B -> A} ->
  s ∘ r ≡ id ->
  Idempotent (s ∘ r)
idempotentSplit {s = s} {r = r} proof rewrite proof =
  record { idempotentProof = refl }

-- examples
-- f : Int -> Bool
-- s : Bool -> Int
-- f = isEven
-- s = toBinary
-- isEven . toBinary = id

open import Agda.Builtin.Nat
open import Data.String

isOdd : Nat -> Bool
isOdd zero = false
isOdd (suc n) = not $ isOdd n

toBinary : Bool -> Nat
toBinary false = zero
toBinary true = suc zero

sectionExample : HasSection (isOdd)
Choice.s sectionExample = toBinary
Choice.choiceProof sectionExample = λ {true -> refl; false -> refl}

-- sectionExample2 : HasSection (toBinary)
-- Choice.s sectionExample2 = isOdd
-- Choice.choiceProof sectionExample2 zero = refl
-- Choice.choiceProof sectionExample2 (suc zero) = refl
-- Choice.choiceProof sectionExample2 (suc (suc a)) =

JSON = String

data World : Set where
  WorldLiteral : World

record Request : Set where
  field hello : World

open import Data.Maybe

parseJson : JSON -> Maybe Request
parseJson "{ hello: world }" = just $ record { hello = WorldLiteral }
parseJson _ = nothing

serializeJson : Maybe Request -> JSON
serializeJson (just record { hello = WorldLiteral }) = "{ hello: world }"
serializeJson nothing = "{}"

retractExample : HasRetract serializeJson
Determination.r retractExample = parseJson
Determination.determinationProof retractExample =
  λ
    { nothing -> refl
    ; (just (record {hello = WorldLiteral})) -> refl
    }

-- 4. Isomorphisms and automorphisms

record HasIsomorphism {A B : Set} (f : A -> B) : Set where
  field
    f-section : HasSection f
    f-retraction : HasRetract f
    iso-proof : (b : B) -> f-section .Choice.s b ≡ f-retraction .Determination.r b

  f-inverse : B -> A
  f-inverse = f-section .Choice.s

  f-inverse-proof-l : (a : A) -> f-inverse (f a) ≡ a
  f-inverse-proof-l a =
    begin
      (f-inverse (f a))
    ≡⟨ iso-proof (f a) ⟩
      ((Determination.r f-retraction ∘ f) a)
    ≡⟨ Determination.determinationProof f-retraction a ⟩
      a
    ∎

  f-inverse-proof-r : (b : B) -> f (f-inverse b) ≡ b
  f-inverse-proof-r b =
    begin
      f (f-inverse b)
    ≡⟨ Choice.choiceProof f-section b ⟩
      b
    ∎

open HasIsomorphism

isomorphismComposition :
  {A B C : Set} -> {f : A -> B} -> {g : B -> C} ->
  HasIsomorphism f ->
  HasIsomorphism g ->
  HasIsomorphism (g ∘ f)
isomorphismComposition
  {f = f}
  {g = g}
  record { f-section = f-section₁ ; f-retraction = f-retraction₁ ; iso-proof = iso-proof₁ }
  record { f-section = f-section ; f-retraction = f-retraction ; iso-proof = iso-proof } =
  let gs = f-section .Choice.s
      fs = f-section₁ .Choice.s
      gSecProof = f-section .Choice.choiceProof
      fSecProof = f-section₁ .Choice.choiceProof
      gr = Determination.r f-retraction
      fr = Determination.r f-retraction₁
      gRetProof = Determination.determinationProof f-retraction
      fRetProof = Determination.determinationProof f-retraction₁
  in record { f-section =
              chooses
                (fs ∘ gs)
                λ c →
                  begin
                  g (f (fs (gs c)))
                  ≡⟨ cong g (fSecProof (gs c)) ⟩
                  g (f-section .Choice.s c)
                  ≡⟨ gSecProof c ⟩
                  c
                  ∎
            ; f-retraction =
              determines
                (fr ∘ gr)
                λ a →
                  begin
                  (fr ∘ gr ∘ g ∘ f) a
                  ≡⟨ cong fr (gRetProof (f a))⟩
                  (fr ∘ f) a
                  ≡⟨ fRetProof a ⟩
                  a
                  ∎
            ; iso-proof =
                λ b →
                begin
                (fs ∘ gs) b
                ≡⟨ iso-proof₁ (gs b) ⟩
                (fr ∘ gs) b
                ≡⟨ cong fr (iso-proof b)⟩
                (fr ∘ gr) b
                ∎
            }

ex10 : {A B C : Set} -> {f : A -> B} -> {g : B -> C} -> HasIsomorphism f -> HasIsomorphism g -> HasIsomorphism (g ∘ f)
ex10 {f = f} {g} f-iso g-iso =
  record
    { f-section = chooses (f-inverse f-iso ∘ f-inverse g-iso) $ \ a ->
       begin
         (g ∘ f ∘ f-inverse f-iso ∘ f-inverse g-iso) a
       ≡⟨ cong g $ f-inverse-proof-r f-iso $ f-inverse g-iso a ⟩
         (g ∘ f-inverse g-iso) a
       ≡⟨ f-inverse-proof-r g-iso a ⟩
         a
       ∎
    ; f-retraction = determines (f-inverse f-iso ∘ f-inverse g-iso) $ \ a ->
       begin
         (f-inverse f-iso ∘ f-inverse g-iso ∘ g ∘ f) a
       ≡⟨ cong (f-inverse f-iso) $ f-inverse-proof-l g-iso (f a) ⟩
         (f-inverse f-iso ∘ f) a
       ≡⟨ f-inverse-proof-l f-iso a ⟩
         a
       ∎
    ; iso-proof = \ b -> refl
    }

ex11 : HasIsomorphism (forward abIso)
ex11 = record
  { f-section = chooses (backward abIso) (fInverse abIso)
  ; f-retraction = determines (backward abIso) (bInverse abIso)
  ; iso-proof = \x -> refl
  }

-- do it with copatterns!
ex11' : HasIsomorphism (forward abIso)
Choice.s (f-section ex11') = backward abIso
Choice.choiceProof (f-section ex11') = fInverse abIso
Determination.r (f-retraction ex11') = backward abIso
Determination.determinationProof (f-retraction ex11') = bInverse abIso
iso-proof ex11' x = refl

isPapa : SetA -> Bool
isPapa Father = true
isPapa _ = false

ex11₂ : HasIsomorphism isPapa -> ⊥
ex11₂ iso with (trans (sym $ f-inverse-proof-l iso Mother) $ f-inverse-proof-l iso Child)
... | ()

Automorphism : Set -> Set
Automorphism A = Isomorphism A A

hasIso-to-Iso : {A B : Set} {f : A -> B} -> HasIsomorphism f -> Isomorphism A B
forward (hasIso-to-Iso {f = f} iso) = f
backward (hasIso-to-Iso iso) = f-inverse iso
fInverse (hasIso-to-Iso iso) = f-inverse-proof-r iso
bInverse (hasIso-to-Iso iso) = f-inverse-proof-l iso


sym-sym-id : {A B : Set} -> (iso : Isomorphism A B) -> iso ≡ symmetricIso (symmetricIso iso)
sym-sym-id iso = refl

postulate
  extensionality : {S : Set}{T : S -> Set}
                   {f g : (x : S) -> T x} ->
                   ((x : S) -> f x ≡ g x) ->
                   f ≡ g

uip : {A : Set} -> {x y : A} -> (p q : x ≡ y) -> p ≡ q
uip refl refl = refl

iso-ext
    : {A B : Set} {f-iso g-iso : Isomorphism A B}
    -> ((a : A) -> forward f-iso a ≡ forward g-iso a)
    -> ((b : B) -> backward f-iso b ≡ backward g-iso b)
    -> f-iso ≡ g-iso
iso-ext
  {f-iso = record { fInverse = fInverse₁ ; bInverse = bInverse₁ }}
  {g-iso = record { fInverse = fInverse  ; bInverse = bInverse }}
  f-eq b-eq rewrite extensionality f-eq
                  | extensionality b-eq
                  | extensionality (\a -> uip (fInverse a) (fInverse₁ a))
                  | extensionality (\a -> uip (bInverse a) (bInverse₁ a))
                  = refl


sym-fwd-id : {A B : Set} -> (iso : Isomorphism A B) -> reflexiveIso ≡ transitiveIso iso (symmetricIso iso)
sym-fwd-id iso = iso-ext (sym ∘ bInverse iso) \b ->
  begin
    backward reflexiveIso b
  ≡⟨⟩
    b
  ≡⟨ sym $ bInverse iso b ⟩
    (backward iso ∘ forward iso) b
  ≡⟨⟩
    (backward iso ∘ backward (symmetricIso iso)) b
  ≡⟨⟩
    backward (transitiveIso iso (symmetricIso iso)) b
  ∎

sym-bwd-id : {A B : Set} -> (iso : Isomorphism A B) -> reflexiveIso ≡ transitiveIso (symmetricIso iso) iso
sym-bwd-id iso =
  begin
    reflexiveIso
  ≡⟨ sym-fwd-id (symmetricIso iso) ⟩
    transitiveIso (symmetricIso iso) (symmetricIso (symmetricIso iso))
  ≡⟨ cong (transitiveIso (symmetricIso iso)) $ sym $ sym-sym-id iso ⟩
    transitiveIso (symmetricIso iso) iso
  ∎

trans-reflex-iso : {A B : Set} -> (iso : Isomorphism A B) -> iso ≡ transitiveIso iso reflexiveIso
trans-reflex-iso _ = iso-ext (\a -> refl) (\b -> refl)

trans-iso
    : {A B C D : Set}
    -> (isoAB : Isomorphism A B)
    -> (isoBC : Isomorphism B C)
    -> (isoCD : Isomorphism C D)
    -> transitiveIso isoAB (transitiveIso isoBC isoCD) ≡ transitiveIso (transitiveIso isoAB isoBC) isoCD
trans-iso _ _ _ = iso-ext (\a -> refl) (\b -> refl)


-- This is not an iff; the number of autos are the same as the number of isos
-- ONLY IF it has isos in the first place!
autoIsos : {A B : Set} {f : A -> B} -> HasIsomorphism f -> Isomorphism (Automorphism A) (Isomorphism A B)
autoIsos {A} {B} {f} f-iso =
  let F : Automorphism A -> Isomorphism A B
      F α = transitiveIso α $ hasIso-to-Iso f-iso

      S : Isomorphism A B -> Automorphism A
      S g = transitiveIso g $ symmetricIso $ hasIso-to-Iso f-iso
   in record { forward = F
             ; backward = S
             ; fInverse = \a ->
               let iso-of-f = hasIso-to-Iso f-iso
                in
                begin
                  transitiveIso (transitiveIso a (symmetricIso iso-of-f)) iso-of-f
                ≡⟨ sym $ trans-iso a (symmetricIso iso-of-f) iso-of-f ⟩
                  transitiveIso a (transitiveIso (symmetricIso iso-of-f) iso-of-f)
                ≡⟨ cong (transitiveIso a) $ sym $ sym-bwd-id iso-of-f ⟩
                  transitiveIso a reflexiveIso
                ≡⟨ sym $ trans-reflex-iso a ⟩
                  a
                ∎
             ; bInverse = \a ->
               let iso-of-f = hasIso-to-Iso f-iso
                in
                begin
                  transitiveIso (transitiveIso a iso-of-f) (symmetricIso iso-of-f)
                ≡⟨ sym $ trans-iso a iso-of-f (symmetricIso iso-of-f) ⟩
                  transitiveIso a (transitiveIso iso-of-f $ symmetricIso iso-of-f)
                ≡⟨ cong (transitiveIso a) $ sym $ sym-fwd-id iso-of-f ⟩
                  transitiveIso a reflexiveIso
                ≡⟨ sym $ trans-reflex-iso a ⟩
                  a
                ∎
             }

