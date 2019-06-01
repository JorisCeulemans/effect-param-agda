{-# OPTIONS --cubical --rewriting #-}
module EffectParametricity.ValueExtraction where

open import TypeSystem
open import Monads.Monads
open import Monads.Examples
open import Target
open import Functors

-- The modules in this file postulate their arguments instead of taking parameters because the properties of p
-- must hold definitionally when using glue (and therefore we need a rewrite rule).
-- The dummy parameters make sure that the modalities of the postulated arguments are correctly enforced.

module Simplified {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    A :{#} Set ℓ
    f : (M :{#} Premonad ℓ) → type M A → type M A
    κ : Premonad ℓ
    κa : type κ A
    p :{¶} {X :{#} Set ℓ} → type κ X → X
    p-return : {X :{#} Set ℓ} {x : X} → p (return κ x) ≡ x
    p-bind : {X Y :{#} Set ℓ} {κx : type κ X} {q : X → type κ Y} → p (bind κ κx q) ≡ p (q (p κx))

  {-# REWRITE p-return #-}
  {-# REWRITE p-bind #-}

  -- Bridge from (type κ X) to X
  p-bridge :{#} (X : Set ℓ) → 𝕀 → Set ℓ
  p-bridge X = / p {X} /

  -- Bridge from (type κ) to id
  type-op-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-op-bridge i X = p-bridge X i

  -- Bridge in Premonad from κ to id-monad
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-op-bridge i ,
                         [¶ (λ {X :{#} Set ℓ} x → push (p {X}) i (return κ x)) ,
                         [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                              (λ { ((i ≣ i0) = p⊤) → bind κ brx q ;
                                                                   ((i ≣ i1) = p⊤) → q brx})
                                                              (pull (p {Y}) i (q (pull (p {X}) i brx))) ) ,
                         tt ] ] ]

  -- Path from (f κ κa) to (f id-monad (p κa))
  f-path : (i :{#} 𝕀) → p-bridge A i
  f-path i = f (pm-bridge i) (push p i κa)

  -- Path from (p (f κ κa)) to (f id-monad (p κa))
  final-path : (i :{#} 𝕀) → A
  final-path i = pull p i (f-path i)

  -- The reason why this proof consists of more than just (path-to-eq final-path) is that pm-bridge i0
  -- is not exactly κ but κ with the last component (of type ⊤) replaced by tt (which is propositionally but not
  -- definitionally equal to trivial κ).
  thm : p (f κ κa) ≡ f id-premonad (p κa)
  thm = cong (λ x → p (f (premonad [ type κ ,
                                    [¶ (λ {_ :{#} Set ℓ} → return κ) ,
                                    [¶ (λ {_ _ :{#} Set ℓ} → bind κ) ,
                                    x ] ] ])
                          κa))
             (unique-⊤ (trivial κ) tt)
        • path-to-eq final-path

module FullResult {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    F : Functor ℓ ℓ
    A :{#} Set ℓ
    f : (M :{#} Premonad ℓ) → obj F (type M A) → type M A
    κ : Premonad ℓ
    Fa : obj F (type κ A)
    p :{¶} {X :{#} Set ℓ} → type κ X → X
    p-return : {X :{#} Set ℓ} {x : X} → p (return κ x) ≡ x
    p-bind : {X Y :{#} Set ℓ} {κb : type κ X} {q : X → type κ Y} → p (bind κ κb q) ≡ p (q (p κb))

  {-# REWRITE p-return #-}
  {-# REWRITE p-bind #-}

  -- Bridge from (type κ X) to X
  p-bridge :{#} (X : Set ℓ) → 𝕀 → Set ℓ
  p-bridge X = / p {X} /

  -- Bridge from (type κ) to (type id-premonad)
  type-op-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-op-bridge i X = p-bridge X i

  -- Bridge in Premonad from κ to id-premonad
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-op-bridge i ,
                         [¶ (λ {X :{#} Set ℓ} x → push (p {X}) i (return κ x)) ,
                         [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                              (λ { ((i ≣ i0) = p⊤) → bind κ brx q ;
                                                                   ((i ≣ i1) = p⊤) → q brx})
                                                              (pull (p {Y}) i (q (pull (p {X}) i brx))) ) ,
                         tt ] ] ]

  -- Path from (hom F id Fa) to (hom F p Fa)
  Fa-path : (i :{#} 𝕀) → obj F (type-op-bridge i A)
  Fa-path i = hom F (push p i) Fa

  -- Path from (f κ (hom F id Fa)) to (f id-premonad (hom F p Fa))
  f-path : (i :{#} 𝕀) → type-op-bridge i A
  f-path i = f (pm-bridge i) (Fa-path i)

  -- Homogeneous path from (p (f κ (hom F id Fa))) to (f id-premonad (hom F p Fa))
  final-path : (i :{#} 𝕀) → A
  final-path i = pull p i (f-path i)

  -- Theorem 2 from Voigtländer (2009)
  -- Just as in the module Simplified, we have here that pm-bridge i0 is not exactly κ.
  thm : p (f κ Fa) ≡ f id-premonad (hom F p Fa)
  thm = cong (λ x → p (f κ x)) (sym (funct-id F))
        • cong (λ x → p (f (premonad [ type κ ,
                                      [¶ (λ {_ :{#} Set _} → return κ) ,
                                      [¶ (λ {_ _ :{#} Set _} → bind κ) ,
                                      x ] ] ])
                            (hom F id Fa)))
               (unique-⊤ (trivial κ) tt)
        • path-to-eq final-path
