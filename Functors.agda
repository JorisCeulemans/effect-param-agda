{-# OPTIONS --cubical --rewriting #-}
module Functors where

open import AlternativeTypeSystem
open import AlternativeSource

record Functor (ℓ : Level) : Set (lsuc ℓ) where
  constructor functor
  field
    unfunctor : Σ[ obj ∈ (Set ℓ → Set ℓ) ] (
                ¶Σ[ hom ∈ ({X Y :{#} Set ℓ} → (X → Y) → obj X → obj Y) ] (
                ¶Σ[ funct-id ∈ ({X :{#} Set ℓ} {x : obj X} → hom id x ≡ x) ] (
                ⊤ )))

open Functor

obj : ∀ {ℓ} → Functor ℓ → Set ℓ → Set ℓ
obj F = fst(unfunctor F)

hom : ∀ {ℓ} (F :{#} Functor ℓ) → {X Y :{#} Set ℓ} → (X → Y) → (obj F X) → (obj F Y)
hom F = ¶fst(snd(unfunctor F))

funct-id : ∀ {ℓ} (F :{#} Functor ℓ) → {X :{#} Set ℓ} → {x : obj F X} → hom F id x ≡ x
funct-id F = ¶fst(¶snd(snd(unfunctor F)))

module SquareCompositionFunctor {ℓ} where
  postulate
    F : Functor ℓ
    A B C D :{#} Set ℓ
    f1 : A → B
    f2 : C → D
    g :{¶} A → C
    h :{¶} B → D
    comm : (a : A) → h (f1 a) ≡ f2 (g a)

  Fid : {X :{#} Set ℓ} → {x : obj F X} → (¶fst (snd (unfunctor F))) id x ≡ x
  Fid = funct-id F

  {-# REWRITE comm #-}
  {-# REWRITE Fid #-}

  g-bridge :{#} 𝕀 → Set ℓ
  g-bridge = / g /

  h-bridge :{#} 𝕀 → Set ℓ
  h-bridge = / h /

  -- Bridge from A → B to C → D
  func-bridge :{#} 𝕀 → Set ℓ
  func-bridge i = (g-bridge i) → (h-bridge i)

  -- Path from a : A to g(a) : C
  g-path : A → (i :{#} 𝕀) → g-bridge i
  g-path a i = push g i a

  -- Path from b : B to h(b) : D
  h-path : B → (i :{#} 𝕀) → h-bridge i
  h-path b i = push h i b

  -- Path from f1 : A → B to f2 : C → D
  func-path : (i :{#} 𝕀) → g-bridge i → h-bridge i
  func-path i x = mweld {φ = (i ≣ i0) ∨ (i ≣ i1)}
                        {C = λ _ → h-bridge i}
                        (λ (a :{#} A) → h-path (f1 a) i)
                        (λ { ((i ≣ i0) = p⊤) → f1 ; ((i ≣ i1) = p⊤) → f2 })
                        x

  -- Path from F f1 : F A → F B to F f2 : F C → F D
  F-path : (i :{#} 𝕀) → obj F (g-bridge i) → obj F (h-bridge i)
  F-path i = hom F (func-path i)

  Fg-path : obj F A → (i :{#} 𝕀) → obj F (g-bridge i)
  Fg-path fa i = (hom F (push g i)) fa

  Fh-pull : (i :{#} 𝕀) → obj F (h-bridge i) → obj F D
  Fh-pull i = hom F (pull h i)

  final-path : (fa : obj F A) (i :{#} 𝕀) → obj F D
  final-path fa i = Fh-pull i (F-path i (Fg-path fa i))

  commF : (fa : obj F A) → hom F h (hom F f1 fa) ≡ hom F f2 ((hom F g) fa)
  commF fa = path-to-eq (final-path fa)

module CompositionFunctorProof {ℓ}
                               (F : Functor ℓ)
                               (A B C :{#} Set ℓ)
                               (f :{¶} A → B)
                               (g :{¶} B → C)
                               where

  -- Bridge from B to C
  g-bridge :{#} 𝕀 → Set ℓ
  g-bridge = / g /

  -- Bridge from A → B to A → C
  func-bridge :{#} 𝕀 → Set ℓ
  func-bridge i = A → (g-bridge i)

  -- Path from b : B to g(b) : C
  g-path : B → (i :{#} 𝕀) → g-bridge i
  g-path b i = push g i b

  -- Path from f : A → B to g ∘ f : A → C
  func-path : (i :{#} 𝕀) → A → g-bridge i
  func-path i a = g-path (f a) i

  -- Path from F f : F A → F B to F (g ∘ f) : F A → F C
  F-path : (i :{#} 𝕀) → obj F A → obj F (g-bridge i)
  F-path i = hom F {A} {g-bridge i} (func-path i)

  Fg-pull : (i :{#} 𝕀) → obj F (g-bridge i) → obj F C
  Fg-pull i = hom F (pull g i)

  final-path : (fa : obj F A) (i :{#} 𝕀) → obj F C
  final-path fa i = Fg-pull i (F-path i fa)

  compF : (fa : obj F A) → hom F g (hom F f fa) ≡ hom F (g ∘ f) fa
  compF fa = path-to-eq (final-path fa) • funct-id F

module Examples where
  id-functor : ∀ {ℓ} → Functor ℓ
  id-functor {ℓ} = functor [ id ,
                           [¶ (λ {X Y :{#} Set ℓ} f → f) ,
                           [¶ (λ {X :{#} Set ℓ} {x} → refl x) ,
                           tt ] ] ]

  map-id : ∀ {ℓ} {A :{#} Set ℓ} {l : List A} → map id l ≡ l
  map-id {_} {A} {l} = list {B = (λ la → map id la ≡ la)} (refl []) (λ a as result-as → cong (λ x → a :: x) result-as) l

  map-id' : ∀ {ℓ} {A :{#} Set ℓ} → map (id {_} {A}) ≡ id
  map-id' = funext (λ as → map-id {l = as})

  list-functor : ∀ {ℓ} → Functor ℓ
  list-functor {ℓ} = functor [ List ,
                             [¶ (λ {X Y :{#} Set ℓ} f → map f) ,
                             [¶ (λ {X :{#} Set ℓ} {xs : List X} → map-id) ,
                             tt ] ] ]

open Examples public
