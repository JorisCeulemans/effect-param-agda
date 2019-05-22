{-# OPTIONS --cubical --rewriting #-}
module EffectParametricity.Voigtlaender where

open import TypeSystem
open import Functors
open import Monads.Monads
open import Monads.Examples

sequence : ∀ {ℓ} (μ :{#} Premonad ℓ) {X :{#} Set ℓ} → List (type μ X) → type μ (List X)
sequence μ l = list (return μ []) (λ mx lt seq-lt → bind μ mx (λ x → bind μ seq-lt (λ ltx → return μ (x :: ltx)))) l

f2 : (μ :{#} Premonad lzero) → List (type μ Nat) → type μ Nat
f2 μ ms = bind μ (sequence μ ms) (λ lnat → return μ (sum lnat))

f3 : (μ :{#} Premonad lzero) → List (type μ Nat) → type μ Nat
f3 μ = (f2 μ) ∘ reverse

-- f4 : ∀ {ℓ} (μ :{#} Premonad ℓ) → List (type μ Nat) → type μ Nat
-- f4 μ l = list (return μ zero) (λ m ms f4ms → {!!}) l


module Purity {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  open import Source

  postulate
    A :{#} Set ℓ
    f : (μ :{#} Premonad ℓ) → List (type μ A) → type μ A
    κ : Premonad ℓ
    κmon : IsMonad κ
    l' : List A
    
  κ-return-law1 : {X Y :{#} Set ℓ} {x : X} {q : X → type κ Y} →  ¶fst (¶snd (snd (unpremonad κ))) (¶fst (snd (unpremonad κ)) x) q ≡ q x
  κ-return-law1 = return-law1 κmon

  {-# REWRITE κ-return-law1 #-}

  -- Bridge from X to (type κ X)
  return-bridge :{#} (X : Set ℓ) → 𝕀 → Set ℓ
  return-bridge X = / return κ {X} /

  -- Bridge from (type id-premonad) to (type κ)
  type-constr-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constr-bridge i X = return-bridge X i
  
  -- Bridge from id-premonad to κ
  premonad-bridge :{#} 𝕀 → Premonad ℓ
  premonad-bridge i = premonad [ type-constr-bridge i ,
                               [¶ (λ {X :{#} Set ℓ} → push (return κ {X}) i) ,
                               [¶ (λ bx q → mweld q (λ { ((i ≣ i0) = p⊤) → q ; ((i ≣ i1) = p⊤) → (λ bx → bind κ bx q)}) bx) ,
                               tt ] ] ]

  -- Path from l' to (map (return κ) l')
  l'-path : (i :{#} 𝕀) → List (type-constr-bridge i A)
  l'-path i = map (push (return κ) i) l'

  -- Path from (f id-premonad l') to (f κ (map (return κ) l'))
  fpath : (i :{#} 𝕀) → type-constr-bridge i A
  fpath i = f (premonad-bridge i) (l'-path i)

  -- Path from (return κ (f id-premonad l')) to (f κ (map (return κ) l'))
  final-path : (i :{#} 𝕀) → type κ A
  final-path i = pull (return κ) i (fpath i)

  thm : return κ (f id-premonad l') ≡ f κ (map (return κ) l')
  thm = cong (λ l → return κ (f id-premonad l)) (sym map-id) • path-to-eq final-path • {!!}
{-
module ValueExtraction where
  open import AlternativeTarget

  postulate
    f : (μ :{#} Premonad ℓ) → List (type μ Nat) → type μ Nat
    κ' : Premonad ℓ

  κ : Premonad ℓ
  κ = premonad [ type κ' ,
               [¶ (λ {X :{#} Set ℓ} → return κ' {X}) ,
               [¶ (λ {X Y :{#} Set ℓ} → bind κ' {X} {Y}) ,
               tt ] ] ]

  postulate
    l : List (type κ Nat)
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

  -- Bridge in Premonad from κ to id-premonad
  premonad-bridge :{#} 𝕀 → Premonad ℓ
  premonad-bridge i = premonad [ type-constr-bridge i ,
                               [¶ (λ {X :{#} Set ℓ} x → push (p {X}) i (return κ x)) ,
                               [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                                  (λ { ((i ≣ i0) = p⊤) → bind κ brx q ;
                                                                       ((i ≣ i1) = p⊤) → q brx})
                                                                  (pull (p {Y}) i (q (pull (p {X}) i brx))) ) ,
                               tt ] ] ]

  -- Path from l to (map p l)
  l-path : (i :{#} 𝕀) → List (type-constr-bridge i Nat)
  l-path i = map (push p i) l

  -- Path from (f κ l) to (f id-premonad (map p l))
  f-path : (i :{#} 𝕀) → type-constr-bridge i Nat
  f-path i = f (premonad-bridge i) (l-path i)

  -- Path from (p (f κ l)) to (f id-monad (map p l))
  final-path : (i :{#} 𝕀) → Nat
  final-path i = pull p i (f-path i)

  thm : p (f κ l) ≡ f id-premonad (map p l)
  thm = cong (λ x → p (f κ x)) (sym map-id) • path-to-eq final-path

module MonadMorphism where
  open import AlternativeTarget
  
  postulate
    f : (μ :{#} Premonad ℓ) → List (type μ Nat) → type μ Nat
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
    h :{¶} PremonadMorphism κ1 κ2
    l' : List (type κ1 Nat)

  h-return-law : {X :{#} Set ℓ} {x : X} → fst (unmonad-morphism h) (¶fst (snd (unpremonad κ1)) x) ≡ return κ2 x
  h-return-law = morph-return-law {h = h}

  h-bind-law : {X Y :{#} Set ℓ} {mx : type κ1 X} {q : X → type κ1 Y}
                     → fst (unmonad-morphism h) (¶fst (¶snd (snd (unpremonad κ1))) mx q) ≡ bind κ2 (morphism h mx) ((morphism h) ∘ q)
  h-bind-law = morph-bind-law {κ1} {κ2} {h}

  {-# REWRITE h-return-law #-}
  {-# REWRITE h-bind-law #-}

  -- Bridge from (type κ1 X) to (type κ2 X)
  h-bridge :{#} Set ℓ → 𝕀 → Set ℓ
  h-bridge X = / morphism h {X} /

  -- Bridge from (type κ1) to (type κ2)
  type-constr-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constr-bridge i X = h-bridge X i

  -- Bridge from κ1 to κ2
  premonad-bridge :{#} 𝕀 → Premonad ℓ
  premonad-bridge i = premonad [ type-constr-bridge i ,
                               [¶ (λ {X :{#} Set ℓ} x → push (morphism h {X}) i (return κ1 x) ) ,
                               [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                                  (λ { ((i ≣ i0) = p⊤) → bind κ1 brx q ;
                                                                       ((i ≣ i1) = p⊤) → bind κ2 brx q })
                                                                  (bind κ2 (pull (morphism h {X}) i brx) ((pull (morphism h {Y}) i) ∘ q)) ) ,
                               tt ] ] ]

  -- Path from l' to (map h l')
  path-l' : (i :{#} 𝕀) → List (type-constr-bridge i Nat)
  path-l' i = map (push (morphism h) i) l'

  -- Path from (f κ1 l') to (f κ2 (map h l'))
  path-f : (i :{#} 𝕀) → type-constr-bridge i Nat
  path-f i = f (premonad-bridge i) (path-l' i)

  -- Path from (h (f κ1 l')) to (f κ2 (map h l'))
  final-path : (i :{#} 𝕀) → type κ2 Nat
  final-path i = pull (morphism h) i (path-f i)

  thm : morphism h (f κ1 l') ≡ f κ2 (map (morphism h) l')
  thm = cong (λ x → morphism h (f κ1 x)) (sym map-id) • path-to-eq final-path

module MorePolymorphic where
  open import AlternativeTarget

  postulate
    f : (μ :{#} Premonad ℓ) {X :{#} Set ℓ} → List (type μ X) → type μ (List X)
    κ1' : Monad
    κ2' : Monad

  κ1 : Premonad ℓ
  κ1 = monad-to-pre κ1'
  
  κ2 : Premonad ℓ
  κ2 = monad-to-pre κ2'

  postulate
    h : PreMonadMorphism κ1 κ2
    A B : Set ℓ
    g : A → B
    l : List (type κ1 A)

  h-return-law : {X :{#} Set ℓ} {x : X} → fst (unmonad-morphism h) (¶fst (snd (unpremonad κ1)) x) ≡ return κ2 x
  h-return-law = morph-return-law {h = h}

  h-bind-law : {X Y :{#} Set ℓ} {mx : type κ1 X} {q : X → type κ1 Y}
                     → fst (unmonad-morphism h) (¶fst (¶snd (snd (unpremonad κ1))) mx q) ≡ bind κ2 (morphism h mx) ((morphism h) ∘ q)
  h-bind-law = morph-bind-law {κ1} {κ2} {h}

  {-# REWRITE h-return-law #-}
  {-# REWRITE h-bind-law #-}

  -- Bridge from (type κ1 X) to (type κ2 X)
  h-bridge :{#} Set ℓ → 𝕀 → Set ℓ
  h-bridge X = / morphism h {X} /

  -- Bridge from (type κ1) to (type κ2)
  type-constr-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constr-bridge i X = h-bridge X i

  -- Bridge from κ1 to κ2
  premonad-bridge :{#} 𝕀 → Premonad ℓ
  premonad-bridge i = premonad [ type-constr-bridge i ,
                               [¶ (λ {X :{#} Set ℓ} x → push (morphism h {X}) i (return κ1 x) ) ,
                               [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                                  (λ { ((i ≣ i0) = p⊤) → bind κ1 brx q ;
                                                                       ((i ≣ i1) = p⊤) → bind κ2 brx q })
                                                                  (bind κ2 (pull (morphism h {X}) i brx) ((pull (morphism h {Y}) i) ∘ q)) ) ,
                               tt ] ] ]

  -- Path from l to (map h l)
  hl-path : (i :{#} 𝕀) → List (type-constr-bridge i A)
  hl-path i = map (push (morphism h) i) l

  -- Bridge from A to B
  g-bridge :{#} 𝕀 → Set ℓ
  g-bridge = / g /

  -- Path from l to ((map (fmap κ2 g)) (map h l))
  ghl-path : (i :{#} 𝕀) → List (type-constr-bridge i (g-bridge i))
  ghl-path i = map (pre-fmap (premonad-bridge i) (push g i)) (hl-path i)

  -- Path from (f κ1 l) to (f κ2 ((map (fmap κ2 g)) (map h l)))
  f-path : (i :{#} 𝕀) → type-constr-bridge i (List (g-bridge i))
  f-path i = f (premonad-bridge i) (ghl-path i)

  -- Path from (h (f κ1 l)) to (f κ2 ((map (fmap κ2 g)) (map h l)))
  almost-final-path : (i :{#} 𝕀) → type κ2 (List (g-bridge i))
  almost-final-path i = pull (morphism h) i (f-path i)

  -- Path from ((fmap κ2 (map g)) (h (f κ1 l))) to (f κ2 ((map (fmap κ2 g)) (map h l)))
  final-path : (i :{#} 𝕀) → type κ2 (List B)
  final-path i = (pre-fmap κ2 (map (pull g i))) (almost-final-path i)

  thm : pre-fmap κ2 (map g) (morphism h (f κ1 l)) ≡ f κ2 ((map (pre-fmap κ2 g)) (map (morphism h) l))
  thm = cong (λ z → pre-fmap κ2 (map g) (morphism h (f κ1 z))) (sym map-id) •
        cong (λ z → pre-fmap κ2 (map g) (morphism h (f κ1 (map z l)))) (funext (λ z → sym (fmap-id κ1'))) •
        cong (λ z → pre-fmap κ2 (map g) (morphism h (f κ1 (map (pre-fmap κ1 id) z)))) (sym (map-id {l = l})) •
        path-to-eq final-path •
        cong (λ z → bind κ2 (almost-final-path i1) (return κ2 ∘ z)) map-id' •
        return-law2 κ2'
-}
