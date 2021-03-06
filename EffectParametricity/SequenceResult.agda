{-# OPTIONS --cubical --rewriting #-}

open import TypeSystem
open import Functors
open import Monads.Monads
open import Monads.Examples
open import Target

-- The module in this file postulates its arguments instead of taking parameters because the monad morphism laws
-- must hold definitionally when using glue (and therefore we need a rewrite rule).
-- The dummy parameters make sure that the modalities of the postulated arguments are correctly enforced.

-- The premonads κ1 and κ2 could also be postulated with a continuous modality if we defined h as a polymorphic map
-- of type {X :{#} Set ℓ} → type κ1 X → type κ2 X and additionally postulated the laws that turn h into a
-- monad morphism.

module EffectParametricity.SequenceResult {ℓ} {iddummy : Set} {pardummy :{#} Set} where
  postulate
    F :{#} Functor ℓ ℓ
    f : (M :{#} Premonad ℓ) {X :{#} Set ℓ} → obj F (type M X) → type M (obj F X)
    κ1 :{¶} Premonad ℓ
    κ1mon : IsMonad κ1
    κ2 :{¶} Premonad ℓ
    κ2mon : IsMonad κ2
    h :{¶} MonadMorphism κ1 κ2
    A B :{#} Set ℓ
    g :{¶} A → B
    Fκ1a : obj F (type κ1 A)

  h-return-law :{¶} {X :{#} Set ℓ} {x : X} → fst (unmonad-morphism h) (¶fst (snd (unpremonad κ1)) x) ≡ return κ2 x
  h-return-law = morph-return-law {h = h}

  h-bind-law :{¶} {X Y :{#} Set ℓ} {mx : type κ1 X} {q : X → type κ1 Y}
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
                                                              (bind κ2 (pull (morphism h {X}) i brx) ((pull (morphism h {Y}) i) ∘ q))) ,
                         tt ] ] ]

  -- Path from (hom F id Fκ1a) to (hom F h Fκ1a)
  hFκ1a-path : (i :{#} 𝕀) → obj F (type-op-bridge i A)
  hFκ1a-path i = hom F (push (morphism h) i) Fκ1a

  -- Bridge from A to B
  g-bridge :{#} 𝕀 → Set ℓ
  g-bridge = / g /

  -- Path from (hom F (fmap κ1 id) (hom F id Fκ1a)) to (hom F (fmap κ2 g)) (hom F h Fκ1a)
  ghFκ1a-path : (i :{#} 𝕀) → obj F (type-op-bridge i (g-bridge i))
  ghFκ1a-path i = hom F (fmap (pm-bridge i) (push g i)) (hFκ1a-path i)

  -- Path from (f κ1 (hom F (fmap κ1 id) (hom F id Fκ1a))) to (f κ2 ((hom F (fmap κ2 g)) (hom F h Fκ1a)))
  f-path : (i :{#} 𝕀) → type-op-bridge i (obj F (g-bridge i))
  f-path i = f (pm-bridge i) (ghFκ1a-path i)

  -- Path from (h (f κ1 (hom F (fmap κ1 id) (hom F id Fκ1a)))) to (f κ2 ((hom F (fmap κ2 g)) (hom F h Fκ1a)))
  almost-final-path : (i :{#} 𝕀) → type κ2 (obj F (g-bridge i))
  almost-final-path i = pull (morphism h) i (f-path i)

  -- Homogeneous path from (fmap κ2 (hom F g) (h (f κ1 (hom F (fmap κ1 id) (hom F id Fκ1a)))))
  -- to (fmap κ2 (hom F id) (f κ2 ((hom F (fmap κ2 g)) (hom F h Fκ1a))))
  final-path : (i :{#} 𝕀) → type κ2 (obj F B)
  final-path i = (fmap κ2 (hom F (pull g i))) (almost-final-path i)

  -- Theorem 5 from Voigtländer (2009)
  -- The reason why this proof consists of more than just (path-to-eq final-path) is that pm-bridge i0
  -- is not exactly κ1 but κ1 with the last component (of type ⊤) replaced by tt (which is propositionally but not
  -- definitionally equal to trivial κ1). Similarly pm-bridge i1 is not exactly κ2. Moreover, the endpoints of
  -- final-path contain some extra applications of functors to the identity function, which we have to explicitly
  -- eliminate to obtain the result.
  thm : fmap κ2 (hom F g) (morphism h (f κ1 Fκ1a)) ≡ f κ2 (hom F (fmap κ2 g) (hom F (morphism h) Fκ1a))
  thm = cong (λ z → fmap κ2 (hom F g) (morphism h (f κ1 z))) (sym (funct-id F))
        • cong (λ z → fmap κ2 (hom F g) (morphism h (f κ1 (hom F z Fκ1a)))) (funext (λ _ → sym (return-law2 κ1mon)))
        • cong (λ z → fmap κ2 (hom F g) (morphism h (f κ1 (hom F (fmap κ1 id) z)))) (sym (funct-id F))
        • cong (λ z → fmap κ2 (hom F g) (morphism h (f (premonad [ type κ1 ,
                                                                  [¶ (λ {_ :{#} Set _} → return κ1) ,
                                                                  [¶ (λ {_ _ :{#} Set _} → bind κ1) ,
                                                                  z ] ] ])
                                                        (hom F (fmap κ1 id) (hom F id Fκ1a)))))
               (unique-⊤ (trivial κ1) tt)
        • path-to-eq final-path
        • cong (λ z → (fmap κ2 (hom F id) (f (premonad [ type κ2 ,
                                                        [¶ (λ {_ :{#} Set _} → return κ2) ,
                                                        [¶ (λ {_ _ :{#} Set _} → bind κ2) ,
                                                        z ] ] ])
                                              ((hom F (fmap κ2 g)) (hom F (morphism h) Fκ1a)))))
               (unique-⊤ tt (trivial κ2))
        • cong (λ z → fmap κ2 z (f κ2 (hom F (fmap κ2 g) (hom F (morphism h) Fκ1a)))) (funct-id' F)
        • return-law2 κ2mon
