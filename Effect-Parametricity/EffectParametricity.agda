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
  
  -- Bridge from id-premonad to κ
  monad-bridge :{#} 𝕀 → Premonad ℓ
  monad-bridge i = premonad [ type-constructor-bridge i ,
                            [¶ (λ {X :{#} Set ℓ} → push (return κ {X}) i) ,
                            [¶ (λ bx q → mweld q (λ { ((i ≣ i0) = p⊤) → q ; ((i ≣ i1) = p⊤) → (λ bx' → bind κ bx' q)}) bx) ,
                            tt ] ] ]

  -- Path from a to (return κ a)
  areturn-path : (i :{#} 𝕀) → return-bridge A i
  areturn-path i = push (return κ) i a

  -- Path from (f id-premonad a) to (f κ (return κ a))
  fpath : (i :{#} 𝕀) → return-bridge A i
  fpath i = f (monad-bridge i) (areturn-path i)

  -- Homogeneous path from (return κ (f id-premonad a)) to  (f κ (return κ a))
  final-path : (i :{#} 𝕀) → type κ A
  final-path i = pull (return κ) i (fpath i)

  thm : return κ (f id-premonad a) ≡ f κ (return κ a)
  thm = path-to-eq final-path • {!cong (λ M → f M (return M a)) (premonad-⊤-irrelevant κ tt)!}
{-
module SimpleExtraction {ℓ} where
  open import Target

  postulate
    f : ∀ {k} (μ :{#} Premonad k) → type μ Bool → type μ Bool
    κt : Premonad ℓ

  κ : Premonad ℓ
  κ = premonad [ type κt ,
               [¶ (λ {X :{#} Set ℓ} → return κt {X}) ,
               [¶ (λ {X Y :{#} Set ℓ} → bind κt {X} {Y}) ,
               tt ] ] ]

  postulate
    κb : type κ Bool
    p :{¶} {X :{#} Set ℓ} → type κ X → X
    p-return :{¶} {X :{#} Set ℓ} {x : X} → p (return κ x) ≡ x
    p-bind : {X Y :{#} Set ℓ} {κb : type κ X} {q : X → type κ Y} → p (bind κ κb q) ≡ p (q (p κb))

  {-# REWRITE p-return #-}
  {-# REWRITE p-bind #-}

  -- Bridge from (type κ X) to X
  p-bridge :{#} (X : Set ℓ) → 𝕀 → Set ℓ
  p-bridge X = / p {X} /

  -- Bridge from (type κ) to id
  type-constr-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constr-bridge i X = p-bridge X i

  -- Bridge in Monad from κ to id-monad
  monad-bridge :{#} 𝕀 → Premonad ℓ
  monad-bridge i = premonad [ type-constr-bridge i ,
                            [¶ (λ {X :{#} Set ℓ} x → push (p {X}) i (return κ x)) ,
                            [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                               (λ { ((i ≣ i0) = p⊤) → bind κ brx q ;
                                                                    ((i ≣ i1) = p⊤) → q brx})
                                                               (pull (p {Y}) i (q (pull (p {X}) i brx))) ) ,
                            tt ] ] ]

  -- Path from (f κ κb) to (f id-monad (p κb))
  κb-path : (i :{#} 𝕀) → p-bridge Bool i
  κb-path i = f (monad-bridge i) (push p i κb)

  -- Path from (p (f κ κb)) to (f id-monad (p κb))
  final-path : (i :{#} 𝕀) → Bool
  final-path i = pull p i (κb-path i)

  thm : p (f κ κb) ≡ f id-premonad (p κb)
  thm = path-to-eq final-path
-- thm = path-to-eq final-path • cong (λ pm → f (premonad [ (λ X → X) , pm ]) (p κb)) (cong (λ (pm :{¶} _) → [¶ (λ {X :{#} Set ℓ} x → {!pm!}) , [¶ (λ {X Y :{#} Set ℓ} brx q → q brx) , tt ] ]) p-return)
{-
  unit-eq : {x : ⊤} → x ≡ tt
  unit-eq {x} = unit {A = λ y → y ≡ tt} (refl tt) x

  test : κ ≡ κt
  test = cong (λ x → premonad [ fst (unpremonad κt) , [¶ (λ {X :{#} Set ℓ} → ¶fst (snd (unpremonad κt))) , [¶ (λ {X Y :{#} Set ℓ} → ¶fst (¶snd (snd (unpremonad κt)))) , x ] ] ]) (sym (unit-eq {¶snd (¶snd (snd (unpremonad κt)))}))
-}
module MonadMorphismResult {ℓ} where
  open import Target
  
  postulate
    f : ∀ {k} (μ :{#} Premonad k) → type μ Bool → type μ Bool
    κ1' :{¶} Premonad ℓ
    κ2' :{¶} Premonad ℓ

  κ1 : Premonad ℓ
  κ1 = premonad [ type κ1' ,
               [¶ (λ {X :{#} Set ℓ} → return κ1' {X}) ,
               [¶ (λ {X Y :{#} Set ℓ} → bind κ1' {X} {Y}) ,
               tt ] ] ]

  κ2 : Premonad ℓ
  κ2 = premonad [ type κ2' ,
               [¶ (λ {X :{#} Set ℓ} → return κ2' {X}) ,
               [¶ (λ {X Y :{#} Set ℓ} → bind κ2' {X} {Y}) ,
               tt ] ] ]

  postulate
    h :{¶} MonadMorphism κ1 κ2
    κ1b : type κ1 Bool

  h-return-law : {X :{#} Set ℓ} {x : X} → fst (unmonad-morphism h) (¶fst (snd (unpremonad κ1)) x) ≡ return κ2 x
  h-return-law = morph-return-law {h = h}

  h-bind-law : {X Y :{#} Set ℓ} {mx : type κ1 X} {q : X → type κ1 Y}
                     → fst (unmonad-morphism h) (¶fst (¶snd (snd (unpremonad κ1))) mx q) ≡ bind κ2 (morphism h mx) ((morphism h) ∘ q)
  h-bind-law = morph-bind-law {κ1} {κ2} {h}

  {-# REWRITE h-return-law #-}
  {-# REWRITE h-bind-law #-}

  h-bridge :{#} Set ℓ → 𝕀 → Set ℓ
  h-bridge X = / morphism h {X} /

  -- Bridge from (type κ1) to (type κ2)
  type-constr-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constr-bridge i X = h-bridge X i

  -- Bridge from κ1 to κ2
  monad-bridge :{#} 𝕀 → Premonad ℓ
  monad-bridge i = premonad [ type-constr-bridge i ,
                            [¶ (λ {X :{#} Set ℓ} x → push (morphism h {X}) i (return κ1 x) ) ,
                            [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                               (λ { ((i ≣ i0) = p⊤) → bind κ1 brx q ;
                                                                    ((i ≣ i1) = p⊤) → bind κ2 brx q })
                                                               (bind κ2 (pull (morphism h {X}) i brx) ((pull (morphism h {Y}) i) ∘ q)) ) ,
                            tt ] ] ]

  -- Path from κ1b to (h κ1b)
  path-κ1b : (i :{#} 𝕀) → h-bridge Bool i
  path-κ1b i = push (morphism h {Bool}) i κ1b

  -- Path from (f κ1 κ1b) to (f κ2 (h κ1b))
  path-f : (i :{#} 𝕀) → h-bridge Bool i
  path-f i = f (monad-bridge i) (path-κ1b i)

  -- Path from (h (f κ1 κ1b)) to (f κ2 (h κ1b))
  final-path : (i :{#} 𝕀) → type κ2 Bool
  final-path i = pull (morphism h {Bool}) i (path-f i)

  thm : morphism h (f κ1 κ1b) ≡ f κ2 (morphism h κ1b)
  thm = path-to-eq final-path
-}
