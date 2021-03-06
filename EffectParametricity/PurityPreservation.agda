{-# OPTIONS --cubical --rewriting #-}
module EffectParametricity.PurityPreservation where

open import TypeSystem
open import Monads.Monads
open import Monads.Examples
open import Source
open import Functors

-- The modules in this file postulate their arguments instead of taking parameters because one of the monad laws
-- must hold definitionally when using mweld (and therefore we need a rewrite rule).
-- The dummy parameters make sure that the modalities of the postulated arguments are correctly enforced.

module Simplified {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    A :{#} Set ℓ
    f : (M :{#} Premonad ℓ) → type M A → type M A
    κ : Premonad ℓ
    κmon : IsMonad κ
    a : A

  κ-return-law1 : {X Y :{#} Set ℓ} {x : X} {q : X → type κ Y} →  ¶fst (¶snd (snd (unpremonad κ))) (¶fst (snd (unpremonad κ)) x) q ≡ q x
  κ-return-law1 = return-law1 κmon

  {-# REWRITE κ-return-law1 #-}

  -- Bridge from X to (type κ X)
  return-bridge :{#} (X : Set ℓ) → 𝕀 → Set ℓ
  return-bridge X = / return κ {X} /

  -- Bridge from (type id-premonad) to (type κ)
  type-op-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-op-bridge i X = return-bridge X i
  
  -- Bridge in Premonad from id-premonad to κ
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-op-bridge i ,
                         [¶ (λ {X :{#} Set ℓ} → push (return κ {X}) i) ,
                         [¶ (λ bx q → mweld q (λ { ((i ≣ i0) = p⊤) → q ; ((i ≣ i1) = p⊤) → (λ bx' → bind κ bx' q)}) bx) ,
                         tt ] ] ]

  -- Path from a to (return κ a)
  returna-path : (i :{#} 𝕀) → return-bridge A i
  returna-path i = push (return κ) i a

  -- Path from (f id-premonad a) to (f κ (return κ a))
  fpath : (i :{#} 𝕀) → return-bridge A i
  fpath i = f (pm-bridge i) (returna-path i)

  -- Homogeneous path from (return κ (f id-premonad a)) to  (f κ (return κ a))
  final-path : (i :{#} 𝕀) → type κ A
  final-path i = pull (return κ) i (fpath i)

  -- The reason why this proof consists of more than just (path-to-eq final-path) is that pm-bridge i1
  -- is not exactly κ but κ with the last component (of type ⊤) replaced by tt (which is propositionally but not
  -- definitionally equal to trivial κ).
  thm : return κ (f id-premonad a) ≡ f κ (return κ a)
  thm = path-to-eq final-path
        • cong (λ x → f (premonad [ type κ ,
                                   [¶ (λ {_ :{#} Set ℓ} → return κ) ,
                                   [¶ (λ {_ _ :{#} Set ℓ} → bind κ) ,
                                   x ] ] ])
                         (return κ a))
               (unique-⊤ tt (trivial κ))

module FullResult {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    F :{#} Functor ℓ ℓ
    A :{#} Set ℓ
    f : (M :{#} Premonad ℓ) → obj F (type M A) → type M A
    κ : Premonad ℓ
    κmon : IsMonad κ
    Fa : obj F A
    
  κ-return-law1 : {X Y :{#} Set ℓ} {x : X} {q : X → type κ Y} →  ¶fst (¶snd (snd (unpremonad κ))) (¶fst (snd (unpremonad κ)) x) q ≡ q x
  κ-return-law1 = return-law1 κmon

  {-# REWRITE κ-return-law1 #-}

  -- Bridge from X to (type κ X)
  return-bridge :{#} (X : Set ℓ) → 𝕀 → Set ℓ
  return-bridge X = / return κ {X} /

  -- Bridge from (type id-premonad) to (type κ)
  type-op-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-op-bridge i X = return-bridge X i
  
  -- Bridge in Premonad from id-premonad to κ
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-op-bridge i ,
                         [¶ (λ {X :{#} Set ℓ} → push (return κ {X}) i) ,
                         [¶ (λ bx q → mweld q (λ { ((i ≣ i0) = p⊤) → q ; ((i ≣ i1) = p⊤) → (λ bx' → bind κ bx' q)}) bx) ,
                         tt ] ] ]

  -- Path from (hom F id Fa) to (hom F (return κ) Fa)
  Fa-path : (i :{#} 𝕀) → obj F (type-op-bridge i A)
  Fa-path i = hom F (push (return κ) i) Fa

  -- Path from (f id-premonad (hom F id Fa)) to (f κ (hom F (return κ) Fa))
  fpath : (i :{#} 𝕀) → type-op-bridge i A
  fpath i = f (pm-bridge i) (Fa-path i)

  -- Homogeneous path from (return κ (f id-premonad (hom F id Fa))) to (f κ (hom F (return κ) Fa))
  final-path : (i :{#} 𝕀) → type κ A
  final-path i = pull (return κ) i (fpath i)

  -- Theorem 1 from Voigtländer (2009)
  -- Just as in the module Simplified, we have here that pm-bridge i1 is not exactly κ.
  thm : return κ (f id-premonad Fa) ≡ f κ (hom F (return κ) Fa)
  thm = cong (λ x → return κ (f id-premonad x)) (sym (funct-id F))
        • path-to-eq final-path
        • cong (λ x → f (premonad [ type κ ,
                                   [¶ (λ {_ :{#} Set _} → return κ) ,
                                   [¶ (λ {_ _ :{#} Set _} → bind κ) ,
                                   x ] ] ])
                         (hom F (return κ) Fa))
               (unique-⊤ tt (trivial κ))
