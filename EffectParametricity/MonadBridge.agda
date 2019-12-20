{-# OPTIONS --cubical --rewriting #-}

module EffectParametricity.MonadBridge where

open import TypeSystem
open import Monads.Monads
open import Target

eta-glue : {ℓ : Level} (A : Set ℓ) (φ : Prop) (T : _) (f :{¶} _) (b : Glue A φ T f) → b ≡ glue {φ = φ} (λ { (φ = p⊤) → b }) (unglue {φ = φ} b)
eta-glue A φ t f b = refl _

--test : {ℓ : Level} (A : Set ℓ) (φ : Prop) (T : .(IsOne φ) → Set ℓ) (f :{¶} .(p : IsOne φ) → T p → A) (a a' : A) (t t' : .(p : IsOne φ) → T p) → t ≡ t' → glue {f = f} t (f {!!} {!!}) ≡ glue {!!} {!!}
--test A φ t f = {!!}

postulate
  ℓ : Level
  A :{#} Set ℓ
  f : (M :{#} Premonad ℓ) → type M A → type M A
  κ1 :{¶} Premonad ℓ
  κ1-mon : IsMonad κ1
  κ2 :{¶} Premonad ℓ
  κ2-mon : IsMonad κ2
  h :{¶} MonadMorphism κ1 κ2
  κ1a : type κ1 A

h-return-law :{¶} {X :{#} Set ℓ} {x : X} → fst (unmonad-morphism h) (¶fst (snd (unpremonad κ1)) x) ≡ return κ2 x
h-return-law = morph-return-law {h = h}

h-bind-law :{¶} {X Y :{#} Set ℓ} {mx : type κ1 X} {q : X → type κ1 Y}
                   → fst (unmonad-morphism h) (¶fst (¶snd (snd (unpremonad κ1))) mx q) ≡ bind κ2 (morphism h mx) ((morphism h) ∘ q)
h-bind-law = morph-bind-law {h = h}

κ1-left-unit : {X Y :{#} Set ℓ} {x : X} {q : X → type κ1 Y} → ¶fst (¶snd (snd (unpremonad κ1))) (¶fst (snd (unpremonad κ1)) x) q ≡ q x
κ1-left-unit = ¶fst (unmonad κ1-mon)

κ2-left-unit : {X Y :{#} Set ℓ} {x : X} {q : X → type κ2 Y} → ¶fst (¶snd (snd (unpremonad κ2))) (¶fst (snd (unpremonad κ2)) x) q ≡ q x
κ2-left-unit = ¶fst (unmonad κ2-mon)

κ1-right-unit : {X :{#} Set ℓ} {kx : type κ1 X} → ¶fst (¶snd (snd (unpremonad κ1))) kx (¶fst (snd (unpremonad κ1))) ≡ kx
κ1-right-unit = ¶fst (¶snd (unmonad κ1-mon))

κ2-right-unit : {X :{#} Set ℓ} {kx : type κ2 X} → ¶fst (¶snd (snd (unpremonad κ2))) kx (¶fst (snd (unpremonad κ2))) ≡ kx
κ2-right-unit = ¶fst (¶snd (unmonad κ2-mon))

κ1-assoc : {X Y Z :{#} Set ℓ} {kx : type κ1 X} {p : X → type κ1 Y} {q : Y → type κ1 Z} →
           ¶fst (¶snd (snd (unpremonad κ1))) (¶fst (¶snd (snd (unpremonad κ1))) kx p) q ≡ bind κ1 kx (λ x → bind κ1 (p x) q)
κ1-assoc = ¶fst (¶snd (¶snd (unmonad κ1-mon)))

κ2-assoc : {X Y Z :{#} Set ℓ} {kx : type κ2 X} {p : X → type κ2 Y} {q : Y → type κ2 Z} →
           ¶fst (¶snd (snd (unpremonad κ2))) (¶fst (¶snd (snd (unpremonad κ2))) kx p) q ≡ bind κ2 kx (λ x → bind κ2 (p x) q)
κ2-assoc = ¶fst (¶snd (¶snd (unmonad κ2-mon)))

{-# REWRITE h-return-law #-}
{-# REWRITE h-bind-law #-}
{-# REWRITE κ1-left-unit #-}
{-# REWRITE κ2-left-unit #-}
{-# REWRITE κ1-right-unit #-}
{-# REWRITE κ2-right-unit #-}
{-# REWRITE κ1-assoc #-}
{-# REWRITE κ2-assoc #-}

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

_≡⟨_⟩_ : ∀ {ℓ} {X :{#} Set ℓ} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p • q

_∎ : ∀ {ℓ} {X :{#} Set ℓ} (x : X) → x ≡ x
x ∎ = refl x

infixr 25 _≡⟨_⟩_

monad-law-br1 : (i : 𝕀) (X Y :{#} Set ℓ) (x : X) (q : X → type (pm-bridge i) Y) → bind (pm-bridge i) (return (pm-bridge i) x) q ≡ q x
monad-law-br1 i X Y x q = bind (pm-bridge i) (return (pm-bridge i) x) q
  ≡⟨ refl _ ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                   (λ { ((i ≣ i0) = p⊤) → bind κ1 (return κ1 x) q ;
                        ((i ≣ i1) = p⊤) → bind κ2 (morphism h (return κ1 x)) q })
                   (bind κ2 (pull (morphism h {X}) i (push (morphism h {X}) i (return κ1 x))) ((pull (morphism h {Y}) i) ∘ q))
  ≡⟨ refl _ ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                   (λ { ((i ≣ i0) = p⊤) → bind κ1 (return κ1 x) q ;
                        ((i ≣ i1) = p⊤) → bind κ2 (return κ2 x) q })
                   (bind κ2 (return κ2 x) ((pull (morphism h {Y}) i) ∘ q))
  ≡⟨ refl _ ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                   (λ { ((i ≣ i0) = p⊤) → q x ;
                        ((i ≣ i1) = p⊤) → q x })
                   (unglue {φ = (i ≣ i0) ∨ (i ≣ i1)} (q x))
  ≡⟨ refl _ ⟩ (q x ∎)

monad-law-br2 : (i : 𝕀) (X :{#} Set ℓ) (bx : type (pm-bridge i) X) → bind (pm-bridge i) bx (return (pm-bridge i)) ≡ bx
monad-law-br2 i X bx = bind (pm-bridge i) bx (return (pm-bridge i))
  ≡⟨ refl _ ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                    (λ { ((i ≣ i0) = p⊤) → bind κ1 bx (return κ1) ;
                         ((i ≣ i1) = p⊤) → bind κ2 bx (return κ2) })
                    (bind κ2 (pull (morphism h {X}) i bx) ((pull (morphism h {X}) i) ∘ (return (pm-bridge i))))
  ≡⟨ refl _ ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                    (λ { ((i ≣ i0) = p⊤) → bind κ1 bx (return κ1) ;
                         ((i ≣ i1) = p⊤) → bind κ2 bx (return κ2) })
                    (bind κ2 (unglue {φ = (i ≣ i0) ∨ (i ≣ i1)} bx) (return κ2))
  ≡⟨ refl _ ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                    (λ { ((i ≣ i0) = p⊤) → bx ;
                         ((i ≣ i1) = p⊤) → bx })
                    (unglue {φ = (i ≣ i0) ∨ (i ≣ i1)} bx)
  ≡⟨ refl _ ⟩ (bx ∎)

monad-law-br3 : (i : 𝕀) (X Y Z :{#} Set ℓ) (bx : type (pm-bridge i) X) (p : X → type (pm-bridge i) Y) (q : Y → type (pm-bridge i) Z) →
                bind (pm-bridge i) (bind (pm-bridge i) bx p) q ≡ bind (pm-bridge i) bx (λ x → bind (pm-bridge i) (p x) q)
monad-law-br3 i X Y Z bx p q = bind (pm-bridge i) (bind (pm-bridge i) bx p) q
  ≡⟨ refl _ ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                    (λ { ((i ≣ i0) = p⊤) → bind κ1 (bind κ1 bx p) q ;
                         ((i ≣ i1) = p⊤) → bind κ2 (bind κ2 bx p) q })
                    (bind κ2 (pull (morphism h {Y}) i (bind (pm-bridge i) bx p)) ((pull (morphism h {Z}) i) ∘ q))
{-    ≡⟨ refl _ ⟩ (glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                    (λ { ((i ≣ i0) = p⊤) → bind κ1 (bind κ1 bx p) q ;
                         ((i ≣ i1) = p⊤) → bind κ2 (bind κ2 bx p) q })
                    (bind κ2 (unglue {φ = (i ≣ i0) ∨ (i ≣ i1)} (glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                                                                     (λ { ((i ≣ i0) = p⊤) → bind κ1 bx p ;
                                                                          ((i ≣ i1) = p⊤) → bind κ2 bx p })
                                                                     (bind κ2 (pull (morphism h {X}) i bx) ((pull (morphism h {Y}) i) ∘ p))))
                             ((pull (morphism h {Z}) i) ∘ q))-}
  ≡⟨ refl _ ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                    (λ { ((i ≣ i0) = p⊤) → bind κ1 (bind κ1 bx p) q ;
                         ((i ≣ i1) = p⊤) → bind κ2 (bind κ2 bx p) q })
                    (bind κ2 (bind κ2 (pull (morphism h {X}) i bx)
                                      ((pull (morphism h {Y}) i) ∘ p))
                             ((pull (morphism h {Z}) i) ∘ q))
  ≡⟨ refl _ ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                    (λ { ((i ≣ i0) = p⊤) → bind κ1 bx (λ x → bind κ1 (p x) q) ;
                         ((i ≣ i1) = p⊤) → bind κ2 bx (λ x → bind κ2 (p x) q) })
                    (bind κ2 (pull (morphism h {X}) i bx) (λ x → bind κ2 (pull (morphism h {Y}) i (p x)) ((pull (morphism h {Z}) i) ∘ q)))
  ≡⟨ refl _ ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                    (λ { ((i ≣ i0) = p⊤) → bind κ1 bx (λ x → bind κ1 (p x) q) ;
                         ((i ≣ i1) = p⊤) → bind κ2 bx (λ x → bind κ2 (p x) q) })
                    (bind κ2 (pull (morphism h {X}) i bx) (pull (morphism h {Z}) i ∘ (λ x → bind (pm-bridge i) (p x) q)))
  ≡⟨ refl _ ⟩ (bind (pm-bridge i) bx (λ x → bind (pm-bridge i) (p x) q) ∎)
