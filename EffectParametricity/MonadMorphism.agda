{-# OPTIONS --cubical --rewriting #-}
module EffectParametricity.MonadMorphism where

open import TypeSystem
open import Monads.Monads
open import Monads.Examples
open import Target
open import Functors

-- The modules in this file postulate their arguments instead of taking parameters because the monad morphism laws
-- must hold definitionally when using glue (and therefore we need a rewrite rule).
-- The dummy parameters make sure that the modalities of the postulated arguments are correctly enforced.

-- The pointwise dependence of these results on the premonads κ1 and κ2 is explained by the fact that the morphism
-- function defined in Monads.Monads takes its two premonads as continuous parameters and hence they must be pointwise
-- if we want to use morphism inside /_/. This would not be needed if instead of the assumptions below, we postulated that
-- h : {X : {#} Set ℓ} → type κ1 X → type κ2 X and additionally postulated the laws making h into a monad morphism.

module Simplified {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    A :{#} Set ℓ
    f : (M :{#} Premonad ℓ) → type M A → type M A
    κ1 :{¶} Premonad ℓ
    κ2 :{¶} Premonad ℓ
    h :{¶} MonadMorphism κ1 κ2
    κ1a : type κ1 A

  h-return-law :{¶} {X :{#} Set ℓ} {x : X} → fst (unmonad-morphism h) (¶fst (snd (unpremonad κ1)) x) ≡ return κ2 x
  h-return-law = morph-return-law {h = h}

  h-bind-law :{¶} {X Y :{#} Set ℓ} {mx : type κ1 X} {q :{¶} X → type κ1 Y}
                     → fst (unmonad-morphism h) (¶fst (¶snd (snd (unpremonad κ1))) mx q) ≡ bind κ2 (morphism h mx) ((morphism h) ∘ q)
  h-bind-law = morph-bind-law {h = h}

  {-# REWRITE h-return-law #-}
  {-# REWRITE h-bind-law #-}

  -- Bridge from (type κ1 X) to (type κ2 X)
  h-bridge :{#} Set ℓ → 𝕀 → Set ℓ
  h-bridge X = / morphism h {X} /

  -- Bridge from (type κ1) to (type κ2)
  type-op-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-op-bridge i X = h-bridge X i

  -- Bridge in Premonad from κ1 to κ2
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-op-bridge i ,
                         [¶ (λ {X :{#} Set ℓ} x → push (morphism h {X}) i (return κ1 x) ) ,
                         [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                              (λ { ((i ≣ i0) = p⊤) → bind κ1 brx q ;
                                                                   ((i ≣ i1) = p⊤) → bind κ2 brx q })
                                                              (bind κ2 (pull (morphism h {X}) i brx) ((pull (morphism h {Y}) i) ∘ q)) ) ,
                         tt ] ] ]

  -- Path from κ1a to (h κ1a)
  κ1a-path : (i :{#} 𝕀) → h-bridge A i
  κ1a-path i = push (morphism h {A}) i κ1a

  -- Path from (f κ1 κ1a) to (f κ2 (h κ1a))
  f-path : (i :{#} 𝕀) → h-bridge A i
  f-path i = f (pm-bridge i) (κ1a-path i)

  -- Path from (h (f κ1 κ1a)) to (f κ2 (h κ1a))
  final-path : (i :{#} 𝕀) → type κ2 A
  final-path i = pull (morphism h {A}) i (f-path i)

  -- The reason why this proof consists of more than just (path-to-eq final-path) is that pm-bridge i0
  -- is not exactly κ1 but κ1 with the last component (of type ⊤) replaced by tt (which is propositionally but not
  -- definitionally equal to trivial κ1). Similarly pm-bridge i1 is not exactly κ2.
  thm : morphism h (f κ1 κ1a) ≡ f κ2 (morphism h κ1a)
  thm = cong (λ x → morphism h (f (premonad [ type κ1 ,
                                             [¶ (λ {_ :{#} Set ℓ} → return κ1) ,
                                             [¶ (λ {_ _ :{#} Set ℓ} → bind κ1) ,
                                             x ] ] ])
                                   κ1a))
             (unique-⊤ (trivial κ1) tt)
        • path-to-eq final-path
        • cong (λ x → f (premonad [ type κ2 ,
                                   [¶ (λ {_ :{#} Set ℓ} → return κ2) ,
                                   [¶ (λ {_ _ :{#} Set ℓ} → bind κ2) ,
                                   x ] ] ])
                         (morphism h κ1a))
               (unique-⊤ tt (trivial κ2))

module FullResult {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    F :{#} Functor ℓ ℓ
    A :{#} Set ℓ
    f : (M :{#} Premonad ℓ) → obj F (type M A) → type M A
    κ1 :{¶} Premonad ℓ
    κ2 :{¶} Premonad ℓ
    h :{¶} MonadMorphism κ1 κ2
    Fκ1a : obj F (type κ1 A)

  h-return-law :{¶} {X :{#} Set ℓ} {x : X} → fst (unmonad-morphism h) (¶fst (snd (unpremonad κ1)) x) ≡ return κ2 x
  h-return-law = morph-return-law {h = h}

  h-bind-law :{¶} {X Y :{#} Set ℓ} {mx : type κ1 X} {q :{¶} X → type κ1 Y}
                     → fst (unmonad-morphism h) (¶fst (¶snd (snd (unpremonad κ1))) mx q) ≡ bind κ2 (morphism h mx) ((morphism h) ∘ q)
  h-bind-law = morph-bind-law {h = h}

  {-# REWRITE h-return-law #-}
  {-# REWRITE h-bind-law #-}

  -- Bridge from (type κ1 X) to (type κ2 X)
  h-bridge :{#} Set ℓ → 𝕀 → Set ℓ
  h-bridge X = / morphism h {X} /

  -- Bridge from (type κ1) to (type κ2)
  type-op-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-op-bridge i X = h-bridge X i

  -- Bridge in Premonad from κ1 to κ2
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-op-bridge i ,
                         [¶ (λ {X :{#} Set ℓ} x → push (morphism h {X}) i (return κ1 x) ) ,
                         [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                              (λ { ((i ≣ i0) = p⊤) → bind κ1 brx q ;
                                                                   ((i ≣ i1) = p⊤) → bind κ2 brx q })
                                                              (bind κ2 (pull (morphism h {X}) i brx) ((pull (morphism h {Y}) i) ∘ q)) ) ,
                         tt ] ] ]

  -- Path from (hom F id Fκ1a) to (hom F h Fκ1a)
  Fκ1a-path : (i :{#} 𝕀) → obj F (type-op-bridge i A)
  Fκ1a-path i = hom F (push (morphism h) i) Fκ1a

  -- Path from (f κ1 (hom F id Fκ1a)) to (f κ2 (hom F h Fκ1a))
  f-path : (i :{#} 𝕀) → type-op-bridge i A
  f-path i = f (pm-bridge i) (Fκ1a-path i)

  -- Homogeneous path from (h (f κ1 (hom F id Fκ1a))) to (f κ2 (hom F h Fκ1a))
  final-path : (i :{#} 𝕀) → type κ2 A
  final-path i = pull (morphism h) i (f-path i)

  -- Theorems 3 and 4 from Voigländer (2009)
  -- Just as in the module Simplified, we have here that pm-bridge i0 is not exactly κ1
  -- and pm-bridge i1 is not exactly κ2.
  thm : morphism h (f κ1 Fκ1a) ≡ f κ2 (hom F (morphism h) Fκ1a)
  thm = cong (λ x → morphism h (f κ1 x)) (sym (funct-id F))
        • cong (λ x → morphism h (f (premonad [ type κ1 ,
                                               [¶ (λ {_ :{#} Set _} → return κ1) ,
                                               [¶ (λ {_ _ :{#} Set _} → bind κ1) ,
                                               x ] ] ])
                                     (hom F id Fκ1a)))
               (unique-⊤ (trivial κ1) tt)
        • path-to-eq final-path
        • cong (λ x → f (premonad [ type κ2 ,
                                   [¶ (λ {_ :{#} Set _} → return κ2) ,
                                   [¶ (λ {_ _ :{#} Set _} → bind κ2) ,
                                   x ] ] ])
                         (hom F (morphism h) Fκ1a))
               (unique-⊤ tt (trivial κ2))
