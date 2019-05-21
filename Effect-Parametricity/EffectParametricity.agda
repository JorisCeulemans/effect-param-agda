{-# OPTIONS --cubical --rewriting #-}
module Effect-Parametricity.EffectParametricity where

open import TypeSystem
open import Monads.Monads
open import Monads.Examples

module PurityPreservation {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  open import Source

  postulate
    A :{#} Set ℓ
    f : (μ :{#} Premonad ℓ) → type μ A → type μ A
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

module SimpleExtraction {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  open import Target

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

module MonadMorphismResult {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  open import Target
  
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
