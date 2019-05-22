{-# OPTIONS --cubical --rewriting #-}
module EffectParametricity.PurityPreservation where

open import TypeSystem
open import Monads.Monads
open import Monads.Examples
open import Source

module Simplified {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    A :{#} Set ℓ
    f : (μ :{#} Premonad ℓ) → type μ A → type μ A
    κ : Premonad ℓ
    κmon : IsMonad κ
    a : A

  κ-return-law1 : {X Y :{#} Set ℓ} {x : X} {q :{¶} X → type κ Y} →  ¶fst (¶snd (snd (unpremonad κ))) (¶fst (snd (unpremonad κ)) x) q ≡ q x
  κ-return-law1 = return-law1 κmon

  {-# REWRITE κ-return-law1 #-}

  -- Bridge from X to (type κ X)
  return-bridge :{#} (X : Set ℓ) → 𝕀 → Set ℓ
  return-bridge X = / return κ {X} /

  -- Bridge from (type id-premonad) to (type κ)
  type-constructor-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constructor-bridge i X = return-bridge X i
  
  -- Bridge in Premonad from id-premonad to κ
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-constructor-bridge i ,
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

  -- Transitivity and the second equality are needed because pm-bridge i1 is not
  -- exactly κ but κ with the last element of type ⊤ replaced with tt.
  thm : return κ (f id-premonad a) ≡ f κ (return κ a)
  thm = path-to-eq final-path
        • cong (λ x → f (premonad [ type κ , [¶ (λ {_ :{#} Set ℓ} → return κ) , [¶ (λ {_ _ :{#} Set ℓ} → bind κ) , x ] ] ]) (return κ a))
               (unique-⊤ tt (trivial κ))
