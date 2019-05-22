{-# OPTIONS --cubical --rewriting #-}
module EffectParametricity.ValueExtraction where

open import TypeSystem
open import Monads.Monads
open import Monads.Examples
open import Target

module Simplified {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    A :{#} Set ℓ
    f : (μ :{#} Premonad ℓ) → type μ A → type μ A
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
  type-constr-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constr-bridge i X = p-bridge X i

  -- Bridge in Premonad from κ to id-monad
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-constr-bridge i ,
                         [¶ (λ {X :{#} Set ℓ} x → push (p {X}) i (return κ x)) ,
                         [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                              (λ { ((i ≣ i0) = p⊤) → bind κ brx q ;
                                                                   ((i ≣ i1) = p⊤) → q brx})
                                                              (pull (p {Y}) i (q (pull (p {X}) i brx))) ) ,
                         tt ] ] ]

  -- Path from (f κ κa) to (f id-monad (p κa))
  κb-path : (i :{#} 𝕀) → p-bridge A i
  κb-path i = f (pm-bridge i) (push p i κa)

  -- Path from (p (f κ κa)) to (f id-monad (p κa))
  final-path : (i :{#} 𝕀) → A
  final-path i = pull p i (κb-path i)

  thm : p (f κ κa) ≡ f id-premonad (p κa)
  thm = cong (λ x → p (f (premonad [ type κ , [¶ (λ {_ :{#} Set ℓ} → return κ) , [¶ (λ {_ _ :{#} Set ℓ} → bind κ) , x ] ] ]) κa) )
             (unique-⊤ (trivial κ) tt)
        • path-to-eq final-path
