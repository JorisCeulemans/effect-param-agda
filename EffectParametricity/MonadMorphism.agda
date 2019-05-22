{-# OPTIONS --cubical --rewriting #-}
module EffectParametricity.MonadMorphism where

open import TypeSystem
open import Monads.Monads
open import Monads.Examples
open import Target

module Simplified {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    A :{#} Set ℓ
    f : (μ :{#} Premonad ℓ) → type μ A → type μ A
    κ1 :{¶} Premonad ℓ
    κ2 :{¶} Premonad ℓ
    h :{¶} MonadMorphism κ1 κ2
    κ1a : type κ1 A

  h-return-law : {X :{#} Set ℓ} {x : X} → fst (unmonad-morphism h) (¶fst (snd (unpremonad κ1)) x) ≡ return κ2 x
  h-return-law = morph-return-law {h = h}

  h-bind-law : {X Y :{#} Set ℓ} {mx : type κ1 X} {q : X → type κ1 Y}
                     → fst (unmonad-morphism h) (¶fst (¶snd (snd (unpremonad κ1))) mx q) ≡ bind κ2 (morphism h mx) ((morphism h) ∘ q)
  h-bind-law = morph-bind-law {h = h}

  {-# REWRITE h-return-law #-}
  {-# REWRITE h-bind-law #-}

  -- Bridge from (type κ1 X) to (type κ2 X)
  h-bridge :{#} Set ℓ → 𝕀 → Set ℓ
  h-bridge X = / morphism h {X} /

  -- Bridge from (type κ1) to (type κ2)
  type-constr-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constr-bridge i X = h-bridge X i

  -- Bridge in Premonad from κ1 to κ2
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-constr-bridge i ,
                         [¶ (λ {X :{#} Set ℓ} x → push (morphism h {X}) i (return κ1 x) ) ,
                         [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                              (λ { ((i ≣ i0) = p⊤) → bind κ1 brx q ;
                                                                   ((i ≣ i1) = p⊤) → bind κ2 brx q })
                                                              (bind κ2 (pull (morphism h {X}) i brx) ((pull (morphism h {Y}) i) ∘ q)) ) ,
                         tt ] ] ]

  -- Path from κ1a to (h κ1a)
  path-κ1a : (i :{#} 𝕀) → h-bridge A i
  path-κ1a i = push (morphism h {A}) i κ1a

  -- Path from (f κ1 κ1a) to (f κ2 (h κ1a))
  path-f : (i :{#} 𝕀) → h-bridge A i
  path-f i = f (pm-bridge i) (path-κ1a i)

  -- Path from (h (f κ1 κ1a)) to (f κ2 (h κ1a))
  final-path : (i :{#} 𝕀) → type κ2 A
  final-path i = pull (morphism h {A}) i (path-f i)

  thm : morphism h (f κ1 κ1a) ≡ f κ2 (morphism h κ1a)
  thm = cong (λ x → morphism h (f (premonad [ type κ1 , [¶ (λ {_ :{#} Set ℓ} → return κ1) , [¶ (λ {_ _ :{#} Set ℓ} → bind κ1) , x ] ] ]) κ1a))
             (unique-⊤ (trivial κ1) tt)
        • path-to-eq final-path
        • cong (λ x → f (premonad [ type κ2 , [¶ (λ {_ :{#} Set ℓ} → return κ2) , [¶ (λ {_ _ :{#} Set ℓ} → bind κ2) , x ] ] ]) (morphism h κ1a))
               (unique-⊤ tt (trivial κ2))

