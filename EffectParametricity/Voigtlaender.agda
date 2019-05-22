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

{-
module Purity {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  open import Source

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

module ValueExtraction {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  open import Target

  postulate
    F : Functor ℓ ℓ
    A :{#} Set ℓ
    f : (μ :{#} Premonad ℓ) → obj F (type μ A) → type μ A
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
  type-constr-bridge :{#} 𝕀 → Set ℓ → Set ℓ
  type-constr-bridge i X = p-bridge X i

  -- Bridge in Premonad from κ to id-premonad
  pm-bridge :{#} 𝕀 → Premonad ℓ
  pm-bridge i = premonad [ type-constr-bridge i ,
                         [¶ (λ {X :{#} Set ℓ} x → push (p {X}) i (return κ x)) ,
                         [¶ (λ {X Y :{#} Set ℓ} brx q → glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                              (λ { ((i ≣ i0) = p⊤) → bind κ brx q ;
                                                                   ((i ≣ i1) = p⊤) → q brx})
                                                              (pull (p {Y}) i (q (pull (p {X}) i brx))) ) ,
                         tt ] ] ]

  -- Path from (hom F id Fa) to (hom F p Fa)
  Fa-path : (i :{#} 𝕀) → obj F (type-constr-bridge i A)
  Fa-path i = hom F (push p i) Fa

  -- Path from (f κ (hom F id Fa)) to (f id-premonad (hom F p Fa))
  f-path : (i :{#} 𝕀) → type-constr-bridge i A
  f-path i = f (pm-bridge i) (Fa-path i)

  -- Homogeneous path from (p (f κ (hom F id Fa))) to (f id-premonad (hom F p Fa))
  final-path : (i :{#} 𝕀) → A
  final-path i = pull p i (f-path i)

  -- Theorem 2 from Voigtländer (2009)
  thm : p (f κ Fa) ≡ f id-premonad (hom F p Fa)
  thm = cong (λ x → p (f κ x)) (sym (funct-id F))
        • cong (λ x → p (f (premonad [ type κ , [¶ (λ {_ :{#} Set _} → return κ) , [¶ (λ {_ _ :{#} Set _} → bind κ) , x ] ] ]) (hom F id Fa)))
               (unique-⊤ (trivial κ) tt)
        • path-to-eq final-path

module MonadMorphism+ {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  open import Target
  
  postulate
    F : Functor ℓ ℓ
    A : Set ℓ
    f : (μ :{#} Premonad ℓ) → obj F (type μ A) → type μ A
    κ1 :{¶} Premonad ℓ
    κ2 :{¶} Premonad ℓ
    h :{¶} MonadMorphism κ1 κ2
    Fκ1a : obj F (type κ1 A)

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

  -- Path from (hom F id Fκ1a) to (hom F h Fκ1a)
  Fκ1a-path : (i :{#} 𝕀) → obj F (type-constr-bridge i A)
  Fκ1a-path i = hom F (push (morphism h) i) Fκ1a

  -- Path from (f κ1 (hom F id Fκ1a)) to (f κ2 (hom F h Fκ1a))
  f-path : (i :{#} 𝕀) → type-constr-bridge i A
  f-path i = f (pm-bridge i) (Fκ1a-path i)

  -- Homogeneous path from (h (f κ1 (hom F id Fκ1a))) to (f κ2 (hom F h Fκ1a))
  final-path : (i :{#} 𝕀) → type κ2 A
  final-path i = pull (morphism h) i (f-path i)

  thm : morphism h (f κ1 Fκ1a) ≡ f κ2 (hom F (morphism h) Fκ1a)
  thm = cong (λ x → morphism h (f κ1 x)) (sym (funct-id F))
        • cong (λ x → morphism h (f (premonad [ type κ1 , [¶ (λ {_ :{#} Set _} → return κ1) , [¶ (λ {_ _ :{#} Set _} → bind κ1) , x ] ] ]) (hom F id Fκ1a)))
               (unique-⊤ (trivial κ1) tt)
        • path-to-eq final-path
        • cong (λ x → f (premonad [ type κ2 , [¶ (λ {_ :{#} Set _} → return κ2) , [¶ (λ {_ _ :{#} Set _} → bind κ2) , x ] ] ]) (hom F (morphism h) Fκ1a))
               (unique-⊤ tt (trivial κ2))
-}
module MorePolymorphic {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  open import Target

  postulate
    F : Functor ℓ ℓ
    f : (μ :{#} Premonad ℓ) {X :{#} Set ℓ} → obj F (type μ X) → type μ (obj F X)
    κ1 :{¶} Premonad ℓ
    κ1mon : IsMonad κ1
    κ2 :{¶} Premonad ℓ
    κ2mon : IsMonad κ2
    h :{¶} MonadMorphism κ1 κ2
    A B :{#} Set ℓ
    g :{¶} A → B
    Fκ1a : obj F (type κ1 A)

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

  -- Path from (hom F id Fκ1a) to (hom F h Fκ1a)
  hFκ1a-path : (i :{#} 𝕀) → obj F (type-constr-bridge i A)
  hFκ1a-path i = hom F (push (morphism h) i) Fκ1a

  -- Bridge from A to B
  g-bridge :{#} 𝕀 → Set ℓ
  g-bridge = / g /

  -- Path from (hom F (fmap κ1 id) Fκ1a) to (hom F (fmap κ2 g)) (hom F h Fκ1a)
  ghFκ1a-path : (i :{#} 𝕀) → obj F (type-constr-bridge i (g-bridge i))
  ghFκ1a-path i = hom F (fmap (pm-bridge i) (push g i)) (hFκ1a-path i)

  -- Path from (f κ1 (hom F (fmap κ1 id) Fκ1a)) to (f κ2 ((hom F (fmap κ2 g)) (hom F h Fκ1a)))
  f-path : (i :{#} 𝕀) → type-constr-bridge i (obj F (g-bridge i))
  f-path i = f (pm-bridge i) (ghFκ1a-path i)

  -- Path from (h (f κ1 (hom F (fmap κ1 id) Fκ1a))) to (f κ2 ((hom F (fmap κ2 g)) (hom F h Fκ1a)))
  almost-final-path : (i :{#} 𝕀) → type κ2 (obj F (g-bridge i))
  almost-final-path i = pull (morphism h) i (f-path i)

  -- Homogeneous path from (fmap κ2 (hom F g) (h (f κ1 (hom F (fmap κ1 id) Fκ1a)))) to (fmap κ2 (hom F id) (f κ2 ((map (fmap κ2 g)) (map h l))))
  final-path : (i :{#} 𝕀) → type κ2 (obj F B)
  final-path i = (fmap κ2 (hom F (pull g i))) (almost-final-path i)

  thm : fmap κ2 (hom F g) (morphism h (f κ1 Fκ1a)) ≡ f κ2 ((hom F (fmap κ2 g)) (hom F (morphism h) Fκ1a))
  thm = cong (λ z → fmap κ2 (hom F g) (morphism h (f κ1 z))) (sym (funct-id F))
        • cong (λ z → fmap κ2 (hom F g) (morphism h (f κ1 (hom F z Fκ1a)))) (funext (λ z → sym (return-law2 κ1mon)))
{-        • (cong (λ z → fmap κ2 (hom F g) (morphism h (f κ1 (hom F (fmap κ1 id) z)))) (sym (refl _))-}
        • cong (λ z → fmap (premonad [ type κ2 ,
                                      [¶ (λ {_ :{#} Set _} → return κ2) ,
                                      [¶ (λ {_ _ :{#} Set _} → bind κ2) ,
                                      z ] ] ])
                            (hom F g) (morphism h (f κ1 (hom F (fmap κ1 id) Fκ1a))))
               (unique-⊤ (trivial κ2) tt)
        • cong (λ z → fmap (pm-bridge i1) (hom F g) (morphism h (f (premonad [ type κ1 ,
                                                                              [¶ (λ {_ :{#} Set _} → return κ1) ,
                                                                              [¶ (λ {_ _ :{#} Set _} → bind κ1) ,
                                                                              z ] ] ])
                                                                    (hom F (fmap κ1 id) Fκ1a))))
               (unique-⊤ (trivial κ1) tt)
        • {!path-to-eq final-path
        • {!?
        • cong (λ z → bind κ2 (almost-final-path i1) (return κ2 ∘ z)) ?
        • return-law2 κ2mon!}!}
