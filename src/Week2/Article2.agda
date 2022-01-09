module Week2.Article2 where

open import Function
open import Data.Empty
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Function.Reasoning

record Isomorphism (A B : Set) : Set where
  field
    f : A → B
    g : B → A
    fInverse : (x : B) -> (f ∘ g) x ≡ id x
    gInverse : (x : A) -> (g ∘ f) x ≡ id x

data SetB : Set where
  Feather : SetB
  Stone : SetB
  Flower : SetB

data SetA : Set where
  Mother : SetA
  Father : SetA
  Child : SetA

abIso : Isomorphism SetA SetB
Isomorphism.f abIso Mother = Feather
Isomorphism.f abIso Father = Stone
Isomorphism.f abIso Child = Flower
Isomorphism.g abIso Feather = Mother
Isomorphism.g abIso Stone = Father
Isomorphism.g abIso Flower = Child
Isomorphism.fInverse abIso Feather = refl
Isomorphism.fInverse abIso Stone = refl
Isomorphism.fInverse abIso Flower = refl
Isomorphism.gInverse abIso Mother = refl
Isomorphism.gInverse abIso Father = refl
Isomorphism.gInverse abIso Child = refl

reflexiveIso : {A : Set} -> Isomorphism A A
reflexiveIso = record
                 { f = λ z → z
                 ; g = λ z → z
                 ; fInverse = λ x → refl
                 ; gInverse = λ x → refl
                 }

symmetricIso : {A B : Set } -> Isomorphism A B -> Isomorphism B A
symmetricIso record { f = f ; g = g ; fInverse = fInverse ; gInverse = gInverse } = record
                                                                                      { f = g ; g = f ; fInverse = gInverse ; gInverse = fInverse }

transitiveIso : {A B C : Set } -> Isomorphism A B -> Isomorphism B C -> Isomorphism A C
transitiveIso
  record { f = f₁ ; g = g₁ ; fInverse = fInverse₁ ; gInverse = gInverse₁ }
  record { f = f ; g = g ; fInverse = fInverse ; gInverse = gInverse } =
    record
      { f = λ z → f (f₁ z)
      ; g = λ z → g₁ (g z)
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
      ; gInverse = λ x →
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
  ((a : A ) -> (gIso .f a ≡ kIso .f a)) ->
  (x : B) ->
  gIso .g x ≡ kIso .g x
uniqInv
  record { f = f₁ ; g = g₁ ; fInverse = fInverse₁ ; gInverse = gInverse₁ } -- gIso
  record { f = f ; g = g ; fInverse = fInverse ; gInverse = gInverse } -- kIso
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
  ((x : B) -> (iso .f ∘ h) x ≡ (iso .f ∘ k) x) ->
  (x : B) -> h x ≡ k x
leftIsoCancellation record { f = f ; g = g ; fInverse = fInverse ; gInverse = gInverse } h k isoEq x =
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
  ((x : A) -> (h ∘ iso .f) x ≡ (k ∘ iso .f) x) ->
  (x : B) -> h x ≡ k x
rightIsoCancellation record { f = f ; g = g ; fInverse = fInverse ; gInverse = gInverse } h k isoEq x =
  begin
  h x
  ≡⟨ cong h (sym (fInverse x)) ⟩
  h (f (g x))
  ≡⟨ isoEq (g x) ⟩
  k (f (g x))
  ≡⟨ cong k (fInverse x) ⟩
  k x
  ∎

invalidIsoCancellation : {A : Set} ->
  (iso : Isomorphism A A) ->
  (v : A) ->
  (∀ {h k a} -> (h ∘ (iso .f)) a ≡ ((iso .f) ∘ k) a -> h a ≡ k a) -> ⊥
invalidIsoCancellation iso v eq = {!!} -- eq f g x
  where
    open Isomorphism iso
