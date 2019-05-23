{-# OPTIONS --cubical --rewriting #-}
module EffectParametricity.PurityPreservation where

open import TypeSystem
open import Monads.Monads
open import Monads.Examples
open import Source
open import Functors

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
  type-constr-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constr-bridge i X = return-bridge X i
  
  -- Bridge in Premonad from id-premonad to κ
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-constr-bridge i ,
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

module FullResult {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    F : Functor ℓ ℓ
    A :{#} Set ℓ
    f : (μ :{#} Premonad ℓ) → obj F (type μ A) → type μ A
    κ : Premonad ℓ
    κmon : IsMonad κ
    Fa : obj F A
    
  κ-return-law1 : {X Y :{#} Set ℓ} {x : X} {q :{¶} X → type κ Y} →  ¶fst (¶snd (snd (unpremonad κ))) (¶fst (snd (unpremonad κ)) x) q ≡ q x
  κ-return-law1 = return-law1 κmon

  {-# REWRITE κ-return-law1 #-}

  -- Bridge from X to (type κ X)
  return-bridge :{#} (X : Set ℓ) → 𝕀 → Set ℓ
  return-bridge X = / return κ {X} /

  -- Bridge from (type id-premonad) to (type κ)
  type-constr-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constr-bridge i X = return-bridge X i
  
  -- Bridge in Premonad from id-premonad to κ
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-constr-bridge i ,
                         [¶ (λ {X :{#} Set ℓ} → push (return κ {X}) i) ,
                         [¶ (λ bx q → mweld q (λ { ((i ≣ i0) = p⊤) → q ; ((i ≣ i1) = p⊤) → (λ bx → bind κ bx q)}) bx) ,
                         tt ] ] ]

  -- Path from (hom F id Fa) to (hom F (return κ) Fa)
  Fa-path : (i :{#} 𝕀) → obj F (type-constr-bridge i A)
  Fa-path i = hom F (push (return κ) i) Fa

  -- Path from (f id-premonad (hom F id Fa)) to (f κ (hom F (return κ) Fa))
  fpath : (i :{#} 𝕀) → type-constr-bridge i A
  fpath i = f (pm-bridge i) (Fa-path i)

  -- Homogeneous path from (return κ (f id-premonad (hom F id Fa))) to (f κ (hom F (return κ) Fa))
  final-path : (i :{#} 𝕀) → type κ A
  final-path i = pull (return κ) i (fpath i)

  -- Theorem 1 from Voigtländer (2009)
  thm : return κ (f id-premonad Fa) ≡ f κ (hom F (return κ) Fa)
  thm = cong (λ x → return κ (f id-premonad x)) (sym (funct-id F))
        • path-to-eq final-path
        • cong (λ x → f (premonad [ type κ , [¶ (λ {_ :{#} Set _} → return κ) , [¶ (λ {_ _ :{#} Set _} → bind κ) , x ] ] ]) (hom F (return κ) Fa))
               (unique-⊤ tt (trivial κ))
