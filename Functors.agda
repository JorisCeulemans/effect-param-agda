{-# OPTIONS --cubical --rewriting #-}
module Functors where

open import TypeSystem
open import Source

record Functor (k ℓ : Level) : Set (lsuc (k ⊔ ℓ)) where
  constructor functor
  field
    unfunctor : Σ[ obj ∈ (Set k → Set ℓ) ] (
                ¶Σ[ hom ∈ ({X Y :{#} Set k} → (X → Y) → obj X → obj Y) ] (
                ¶Σ[ funct-id ∈ ({X :{#} Set k} {x : obj X} → hom id x ≡ x) ] (
                ⊤ )))

open Functor

obj : ∀ {k ℓ} → Functor k ℓ → Set k → Set ℓ
obj F = fst(unfunctor F)

hom : ∀ {k ℓ} (F :{#} Functor k ℓ) → {X Y :{#} Set k} → (X → Y) → (obj F X) → (obj F Y)
hom F = ¶fst(snd(unfunctor F))

funct-id : ∀ {k ℓ} (F :{#} Functor k ℓ) → {X :{#} Set k} → {x : obj F X} → hom F id x ≡ x
funct-id F = ¶fst(¶snd(snd(unfunctor F)))

funct-id' : ∀ {k ℓ} (F :{#} Functor k ℓ) {X :{#} Set k} → hom F {X} id ≡ id
funct-id' F = funext (λ x → funct-id F)

_∘funct_ : ∀ {ℓ1 ℓ2 ℓ3} → Functor ℓ2 ℓ3 → Functor ℓ1 ℓ2 → Functor ℓ1 ℓ3
G ∘funct F = functor [ obj G ∘ obj F ,
                     [¶ (λ {X Y :{#} Set _} f → hom G (hom F f)) ,
                     [¶ (λ {X :{#} Set _} {x} → cong (λ h → hom G h x) (funct-id' F) • funct-id G) ,
                     tt ] ] ]

module Composition {k ℓ}
                   (F : Functor k ℓ)
                   (A B C :{#} Set k)
                   (f : A → B)
                   (g :{¶} B → C)
                   where

  -- Bridge from B to C
  g-bridge :{#} 𝕀 → Set k
  g-bridge = / g /

  -- Path from b : B to g(b) : C
  g-path : B → (i :{#} 𝕀) → g-bridge i
  g-path b i = push g i b

  -- Path from f a : B to (g ∘ f) a : C
  func-path : (i :{#} 𝕀) → A → g-bridge i
  func-path i a = g-path (f a) i

  -- Path from F f : F A → F B to F (g ∘ f) : F A → F C
  F-path : (i :{#} 𝕀) → obj F A → obj F (g-bridge i)
  F-path i = hom F (func-path i)

  -- Path from F g : F B → F C to F id : F C → F C
  Fpullg-path : (i :{#} 𝕀) → obj F (g-bridge i) → obj F C
  Fpullg-path i = hom F (pull g i)

  -- Homogeneous path from F g (F f fa) : F C to F id (F (g ∘ f) fa) : F C
  final-path : (fa : obj F A) (i :{#} 𝕀) → obj F C
  final-path fa i = Fpullg-path i (F-path i fa)

  -- Final result
  composition : (fa : obj F A) → hom F g (hom F f fa) ≡ hom F (g ∘ f) fa
  composition fa = path-to-eq (final-path fa) • funct-id F

  -- The term composition' proves directly that hom F g ∘ hom F f ≡ hom F (g ∘ f), which
  -- could also be proved by applying function extensionality to the term composition.
  final-path' : (i :{#} 𝕀) → obj F A → obj F C
  final-path' i = (Fpullg-path i) ∘ (F-path i)

  composition' : (hom F g) ∘ (hom F f) ≡ hom F (g ∘ f)
  composition' = path-to-eq final-path' • cong (λ h → h ∘ (hom F (g ∘ f))) (funct-id' F)

-- The following module postulates its arguments because h ∘ f1 must be definitionally equal
-- to f2 ∘ g in order for the result to hold and hence we need a rewrite rule (definitional
-- equality is needed for using mweld in the definition of func-path).
-- We add dummy parameters so that the modalities of the postulated arguments are correctly enforced.

module SquareCommute {k ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    F :{#} Functor k ℓ
    A B C D :{#} Set k
    f1 : A → B
    f2 : C → D
    g :{¶} A → C
    h :{¶} B → D
    comm : (a : A) → h (f1 a) ≡ f2 (g a)

  {-# REWRITE comm #-}

  -- Bridge from A to C
  g-bridge :{#} 𝕀 → Set k
  g-bridge = / g /

  -- Bridge from B to D
  h-bridge :{#} 𝕀 → Set k
  h-bridge = / h /

  -- Path from b : B to h b : D
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

  -- Path from F id : F A → F A to F g : F A → F B
  Fpushg-path : (i :{#} 𝕀) → obj F A → obj F (g-bridge i)
  Fpushg-path i = hom F (push g i)

  -- Path from F h : F B → F D to F id : F D → F D
  Fpullh-path : (i :{#} 𝕀) → obj F (h-bridge i) → obj F D
  Fpullh-path i = hom F (pull h i)

  -- Homogeneous path from F h (F f1 (F id fa)) : F D to F id (F f2 (F g fa)) : F D
  final-path : (fa : obj F A) (i :{#} 𝕀) → obj F D
  final-path fa i = Fpullh-path i (F-path i (Fpushg-path i fa))

  -- Final result
  square-commute : (fa : obj F A) → hom F h (hom F f1 fa) ≡ hom F f2 (hom F g fa)
  square-commute fa = cong (λ x → hom F h (hom F f1 x)) (sym (funct-id F)) • path-to-eq (final-path fa) • funct-id F

  -- Again the two terms below provide a proof of hom F h ∘ hom F f1 ≡ hom F f2 ∘ hom F g
  -- at the function level. This can also be proved by applying function extensionality
  -- to the term square-commute.
  final-path' : (i :{#} 𝕀) → obj F A → obj F D
  final-path' i = (Fpullh-path i) ∘ (F-path i) ∘ (Fpushg-path i)

  square-commute' : hom F h ∘ hom F f1 ≡ hom F f2 ∘ hom F g
  square-commute' = cong (λ x → hom F h ∘ hom F f1 ∘ x) (sym (funct-id' F))
                    • path-to-eq final-path'
                    • cong (λ x → x ∘ hom F f2 ∘ hom F g) (funct-id' F)

module NaturalTransformation {k ℓ : Level}
                             (F G :{#} Functor k ℓ)
                             (ρ : (X :{#} Set k) → obj F X → obj G X)
                             (A B :{#} Set k)
                             (f :{¶} A → B)
                             where
  -- Bridge from A to B
  f-bridge :{#} 𝕀 → Set k
  f-bridge = / f /

  -- Path from F id : F A → F A to F f : F A → F B
  Fpushf-path : (i :{#} 𝕀) → obj F A → obj F (f-bridge i)
  Fpushf-path i = hom F (push f i)

  -- Path from G f : G A → G B to G id : G B → G B
  Gpullf-path : (i :{#} 𝕀) → obj G (f-bridge i) → obj G B
  Gpullf-path i = hom G (pull f i)

  -- Homogeneous path from G f (ρ A (F id fa)) : G B to G id (ρ B (F f fa))
  final-path : (fa : obj F A) → (i :{#} 𝕀) → obj G B
  final-path fa i = Gpullf-path i (ρ (f-bridge i) (Fpushf-path i fa))

  -- Final result
  naturality : (fa : obj F A) → hom G f (ρ A fa) ≡ ρ B (hom F f fa)
  naturality fa = cong (λ x → hom G f (ρ A x)) (sym (funct-id F)) • path-to-eq (final-path fa) • funct-id G

  -- A direct proof that G f ∘ ρ A ≡ ρ B ∘ F f, this can also be proved from the term naturality
  -- using function extensionality.
  final-path' : (i :{#} 𝕀) → obj F A → obj G B
  final-path' i = Gpullf-path i ∘ ρ (f-bridge i) ∘ Fpushf-path i

  naturality' : hom G f ∘ ρ A ≡ ρ B ∘ hom F f
  naturality' = cong (λ x → hom G f ∘ ρ A ∘ x) (sym (funct-id' F)) • (path-to-eq final-path') • cong (λ x → x ∘ ρ B ∘ hom F f) (funct-id' G)

module Examples where
  id-functor : ∀ {ℓ} → Functor ℓ ℓ
  id-functor {ℓ} = functor [ id ,
                           [¶ (λ {X Y :{#} Set ℓ} f → f) ,
                           [¶ (λ {X :{#} Set ℓ} {x} → refl x) ,
                           tt ] ] ]

  map-id : ∀ {ℓ} {A :{#} Set ℓ} {l : List A} → map id l ≡ l
  map-id {_} {A} {l} = list {B = (λ la → map id la ≡ la)} (refl []) (λ a as result-as → cong (λ x → a :: x) result-as) l

  map-id' : ∀ {ℓ} {A :{#} Set ℓ} → map (id {_} {A}) ≡ id
  map-id' = funext (λ as → map-id {l = as})

  list-functor : ∀ {ℓ} → Functor ℓ ℓ
  list-functor {ℓ} = functor [ List ,
                             [¶ (λ {X Y :{#} Set ℓ} f → map f) ,
                             [¶ (λ {X :{#} Set ℓ} {xs : List X} → map-id) ,
                             tt ] ] ]

  hom-functor : ∀ {k ℓ} (X : Set ℓ) → Functor k (k ⊔ ℓ)
  hom-functor {k} {ℓ} X = functor [ (λ Y → (X → Y)) ,
                                  [¶ (λ {Y₁ Y₂ :{#} Set k} f g → f ∘ g) ,
                                  [¶ (λ {Y :{#} Set k} {g : X → Y} → refl g) ,
                                  tt ] ] ]

  mb-map-id : ∀ {ℓ} {A :{#} Set ℓ} {ma : Maybe A} → mb-map id ma ≡ ma
  mb-map-id {_} {A} {ma} = maybe {B = λ my → mb-map id my ≡ my} (λ x → refl _) (refl _) ma

  maybe-functor : ∀ {ℓ} → Functor ℓ ℓ
  maybe-functor {ℓ} = functor [ Maybe ,
                              [¶ (λ {X Y :{#} Set ℓ} f → mb-map f) ,
                              [¶ (λ {X :{#} Set ℓ} {mx : Maybe X} → mb-map-id) ,
                              tt ] ] ]

open Examples public
