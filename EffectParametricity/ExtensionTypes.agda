{-# OPTIONS --cubical --rewriting #-}

module EffectParametricity.ExtensionTypes where

open import Monads.Monads
open import PointwiseEquality
open import Target
open import TypeSystem

postulate
  _[_] : ∀{ℓ} (A : Set ℓ) → ∀ {φ} → (a :{¶} Partial A φ) → Set ℓ
  cut : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} (a :{¶} A) → A [ (λ {(φ = p⊤) → a}) ]
  paste[_]_ : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} (pa :{¶} Partial A φ) → A [ pa ] → A
  rw-ext-def : ∀{ℓ} {A :{#} Set ℓ} (pa :{¶} Partial A p⊤) (exta : A [ pa ]) → paste[ pa ] exta ≡ pa itIsOne

{-# REWRITE rw-ext-def #-}

postulate
  rw-ext-β : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} (a :{¶} A) → paste[ (λ{(φ = p⊤) → a}) ] cut a ≡ a
  rw-ext-η : ∀{ℓ} {A :{#} Set ℓ} (φ :{#} Prop) (pa :{¶} Partial A φ) (exta :{¶} A [ pa ]) → cut (paste[ pa ] exta) ≡ exta
  
{-# REWRITE rw-ext-β #-}
{-# REWRITE rw-ext-η #-}

ext-subst : ∀{ℓ} (A :{#} Set ℓ) {φ :{#} Prop} {pa pa' :{¶} Partial A φ} → pa ¶≡ pa' → A [ pa ] → A [ pa' ]
ext-subst A = ¶subst (λ y → A [ y ])

glue-cong' : ∀ {la lb} {A :{#} Set la} {φ :{#} Prop} {T :{#} .(IsOne φ) → Set lb} {f :{¶} .(o : IsOne φ) → T o → A} →
             (t t' :{¶} .(o : IsOne φ) → T o) →
             (t-eq : t ¶≡ t') →
             (a : A [ (λ o → f o (t o)) ]) (a' : A [ (λ o → f o (t' o)) ]) →
             ¶subst (λ x → A [ (λ o → f o (x o)) ]) {t} {t'} t-eq a ≡ a' →
             glue {f = f} t (paste[ (λ o → f o (t o)) ] a) ≡ glue t' (paste[ (λ o → f o (t' o)) ] a')
glue-cong' {A = A} {φ} {T} {f = f} t t' t-eq = ¶J t t' t-eq
                                          (λ y w → (a : A [ (λ o → f o (t o)) ]) (a' : A [ (λ o → f o (y o)) ]) →
                                                    ¶subst (λ x → A [ (λ o → f o (x o)) ]) {t} {y} w a ≡ a' →
                                                    glue {f = f} t (paste[ (λ o → f o (t o)) ] a) ≡ glue y (paste[ (λ o → f o (y o)) ] a'))
                                          (λ a a' → cong {B = primGlue A φ T f} (λ x → glue t (paste[ (λ o → f o (t o)) ] x)))


{-
-- Using equality of pointwise pairs (meeting Dominique 20/10/19) ...
glue-cong : ∀ {la lb} {A :{#} Set la} {φ :{#} Prop} {T :{#} .(IsOne φ) → Set lb} {f :{¶} .(o : IsOne φ) → T o → A} →
            (p p' : ¶Σ (.(o : IsOne φ) → T o) (λ t → A [ (λ o → f o (t o)) ])) → p ≡ p' →
            glue {f = f} (¶fst p) (paste[ (λ o → f o (¶fst p o)) ] (¶snd p)) ≡ glue (¶fst p') (paste[ (λ o → f o (¶fst p' o)) ] (¶snd p'))
glue-cong {f = f} p p' eq = J eq (λ p' _ → glue {f = f} (¶fst p) (paste[ (λ o → f o (¶fst p o)) ] (¶snd p)) ≡ glue (¶fst p') (paste[ (λ o → f o (¶fst p' o)) ] (¶snd p'))) (refl _)

to-¶Σ-eq' : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} (_ :{¶} A) → Set ℓB}
            {a a' :{¶} A} →
            (a-eq : a ¶≡ a') →
            (b : B a) (b' : B a') →
            ¶subst B a-eq b ≡ b' →
            [¶ a , b ] ≡ [¶ a' , b' ]
to-¶Σ-eq' {B = B}{a}{a'} a-eq = ¶J a a' a-eq
                                  (λ y w → (b : B a) (b' : B y) → ¶subst B w b ≡ b' → [¶ a , b ] ≡ [¶ y , b' ])
                                  (λ b b' → cong (λ z → [¶ a , z ]))

to-¶Σ-eq : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} (_ :{¶} A) → Set ℓB}
           {a a' :{¶} A} →
           (a-eq : a ¶≡ a') →
           {b : B a} {b' : B a'} →
           ¶subst B a-eq b ≡ b' →
           [¶ a , b ] ≡ [¶ a' , b' ]
to-¶Σ-eq a-eq {b} {b'} = to-¶Σ-eq' a-eq b b'

from-¶Σ-eq : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} (_ :{¶} A) → Set ℓB}
             {p p' : ¶Σ A B} →
             p ≡ p' →
             Σ[ fst-eq ∈ ¶fst p ¶≡ ¶fst p' ] (¶subst B fst-eq (¶snd p) ≡ ¶snd p')
from-¶Σ-eq {B = B} {p} p-eq = J p-eq (λ y w → Σ[ fst-eq ∈ ¶fst p ¶≡ ¶fst y ] (¶subst B fst-eq (¶snd p) ≡ ¶snd y)) [ ¶refl (¶fst p) , refl (¶snd p) ]
-}
{-
-- It is probably unsound to postulate congruence for pointwise functions (see mail Andreas 2/1/20).
postulate
  ¶cong : ∀{ℓA ℓB} {A :{#} Set ℓA} {B :{#} Set ℓB} (f : (a :{¶} A) → B) {a a' :{¶} A} → a ≡ a' → f a ≡ f a'
  
ext-subst' : ∀{ℓ} {A : Set ℓ} {φ : Prop} {pa pa' :{¶} Partial A φ} → pa ≡ pa' → A [ pa ] → A [ pa' ]
ext-subst' {_} {A} {φ} {pa} {pa'} eq exta = subst id (¶cong (λ (y :{¶} Partial A φ) → A [ y ]) eq) exta

postulate
  irr-funext : ∀{ℓA ℓB} {A : Set ℓA} {B : Set ℓB} {f g : .A → B} → ((x : A) → f x ≡ g x) → f ≡ g

prop-ext : ∀{ℓ} (A : Set ℓ) {φ : Prop} (pa pa' :{¶} Partial A φ) → (.(o : IsOne φ) → pa o ≡ pa' o) → pa ≡ pa'
prop-ext A {φ} pa pa' eq = irr-funext eq

ext-subst'' : ∀{ℓ} (A : Set ℓ) {φ : Prop} (pa pa' :{¶} Partial A φ) → (.(o : IsOne φ) → pa o ≡ pa' o)  → A [ pa ] → A [ pa' ]
ext-subst'' A {φ} pa pa' eq = ext-subst' (prop-ext A pa pa' eq)

glue-cong' : ∀ {la lb} {A :{#} Set la} {φ :{#} Prop} {T :{#} .(IsOne φ) → Set lb} {f :{¶} .(o : IsOne φ) → T o → A} →
            (t t' :{¶} .(o : IsOne φ) → T o) (a : A [ (λ o → f o (t o)) ]) (a' : A [ (λ o → f o (t' o)) ]) →
            (t=t' : t ≡ t') → ext-subst' (irr-funext (λ o → cong (λ x → f o (x o)) t=t')) a ≡ a' → 
            glue {f = f} t (paste[ (λ o → f o (t o)) ] a) ≡ glue t' (paste[ (λ o → f o (t' o)) ] a')
glue-cong' {A = A} {f = f} t t' a a' t=t' a=a' = {!!}
-}


postulate
  ℓ : Level
  A :{#} Set ℓ
  f : (M :{#} Premonad ℓ) → type M A → type M A
  κ1 :{¶} Premonad ℓ
  κ1-mon : IsMonad κ1
  κ2 :{¶} Premonad ℓ
  κ2-mon : IsMonad κ2
  h :{¶} MonadMorphism κ1 κ2

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
                                                            ((bind κ2 (pull (morphism h {X}) i brx) ((pull (morphism h {Y}) i) ∘ q))) ) ,
                       tt ] ] ]

_≡⟨_⟩_ : ∀ {ℓ} {X :{#} Set ℓ} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p • q

_∎ : ∀ {ℓ} {X :{#} Set ℓ} (x : X) → x ≡ x
x ∎ = refl x

infixr 25 _≡⟨_⟩_
{-
monad-law-br1 : (i : 𝕀) (X Y :{#} Set ℓ) (x :{¶} X) (q :{¶} X → type (pm-bridge i) Y) → bind (pm-bridge i) (return (pm-bridge i) x) q ≡ q x
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
                   (λ { ((i ≣ i0) = p⊤) → bind κ1 (return κ1 x) q ;
                        ((i ≣ i1) = p⊤) → bind κ2 (return κ2 x) q })
                   (paste[ (λ (_ : IsOne ((i ≣ i0) ∨ (i ≣ i1))) → bind κ2 (return κ2 x) ((pull (morphism h {Y}) i) ∘ q)) ] (cut (bind κ2 (return κ2 x) ((pull (morphism h {Y}) i) ∘ q))))
  ≡⟨ glue-cong {φ = {!(i ≣ i0) ∨ (i ≣ i1)!}} [¶ {!!} , {!!} ] {!!} {!!} ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                   (λ { ((i ≣ i0) = p⊤) → q x ;
                        ((i ≣ i1) = p⊤) → q x })
                   (paste[ (λ (_ : IsOne ((i ≣ i0) ∨ (i ≣ i1))) → unglue {φ = (i ≣ i0) ∨ (i ≣ i1)} (q x)) ] cut (unglue {φ = (i ≣ i0) ∨ (i ≣ i1)} (q x)))
  ≡⟨ {!seems rw-ext-β does not work here!} ⟩ glue {φ = (i ≣ i0) ∨ (i ≣ i1)}
                   (λ { ((i ≣ i0) = p⊤) → q x ;
                        ((i ≣ i1) = p⊤) → q x })
                   (unglue {φ = (i ≣ i0) ∨ (i ≣ i1)} (q x))
  ≡⟨ refl _ ⟩ (q x ∎)

-}
