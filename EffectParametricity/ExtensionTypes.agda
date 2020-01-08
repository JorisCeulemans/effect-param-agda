{-# OPTIONS --cubical --rewriting #-}

module EffectParametricity.ExtensionTypes where

open import Monads.Monads
open import PointwiseEquality
open import Target
open import TypeSystem

-- Definition of extension types (taken from https://github.com/Saizan/parametric-demo/tree/experimental)

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


-- Some kind of substitution for extension types.
ext-subst' : ∀ {ℓ} {A :{#} Set ℓ} {φ :{#} Prop} {pa pa' :{¶} Partial A φ} → pa ¶≡ pa' → A [ pa ] → A [ pa' ]
ext-subst' {A = A} = ¶subst (λ y → A [ y ])

-- TODO: ask Andreas whether the following is sound (in particular for the modalities).
postulate
  irr-funext : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} .A → Set ℓB} {f g : .(x : A) → B x} → (.(x : A) → f x ≡ g x) → f ≡ g
  irr-funext-¶eq : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} .A → Set ℓB} {f g :{¶} .(x : A) → B x} → (.(x : A) → f x ¶≡ g x) → f ¶≡ g

partext-¶eq : ∀ {ℓ} {φ :{#} Prop} {A :{#} Partial (Set ℓ) φ} (pa pa' :{¶} PartialP φ (λ o → A o)) →
               PartialP φ (λ o → pa o ¶≡ pa' o) →
               pa ¶≡ pa'
partext-¶eq {A = A} pa pa' e = irr-funext-¶eq {B = A} {f = pa} {g = pa'} e

ext-subst : ∀ {ℓ} {A :{#} Set ℓ} {φ :{#} Prop} (pa pa' :{¶} Partial A φ) →
            PartialP φ (λ o → pa o ¶≡ pa' o) →
            A [ pa ] → A [ pa' ]
ext-subst pa pa' e = ext-subst' (partext-¶eq pa pa' e)

{-
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

glue-cong : ∀ {la lb} {A :{#} Set la} {φ :{#} Prop} {T :{#} .(IsOne φ) → Set lb} {f :{¶} .(o : IsOne φ) → T o → A} →
            {t t' :{¶} .(o : IsOne φ) → T o} →
            {a : A [ (λ o → f o (t o)) ]} {a' : A [ (λ o → f o (t' o)) ]} →
            (t-eq : t ¶≡ t') →
            ¶subst (λ x → A [ (λ o → f o (x o)) ]) {t} {t'} t-eq a ≡ a' →
            glue {f = f} t (paste[ (λ o → f o (t o)) ] a) ≡ glue t' (paste[ (λ o → f o (t' o)) ] a')
glue-cong {t = t}{t'}{a}{a'} t-eq a-eq = glue-cong' t t' t-eq a a' a-eq
-}


-- Glue implemented using extension types (taken from https://github.com/Saizan/parametric-demo/tree/experimental)

Glue⟨_←_,_⟩ : ∀{ℓ} (A : Set ℓ) {φ : Prop} (T : Partial (Set ℓ) φ) (f :{¶} PartialP φ (λ o → T o → A)) → Set ℓ
Glue⟨ A ← T , f ⟩ = Glue A _ T f
glue⟨_↦_⟩ : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} {T :{#} Partial (Set ℓ) φ} {f :{¶} PartialP φ (λ o → T o → A)}
  (t :{¶} PartialP φ T) (exta : A [ (λ{(φ = p⊤) → f _ (t _)}) ]) → Glue⟨ A ← T , f ⟩
glue⟨_↦_⟩ {φ = φ} {f = f} t exta = glue (λ{(φ = p⊤) → t _}) (paste[ (λ{(φ = p⊤) → f _ (t _)}) ] exta)
unglue[_] : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} {T :{#} Partial (Set ℓ) φ} (f :{¶} PartialP φ (λ o → T o → A))
  → Glue⟨ A ← T , f ⟩ → A
unglue[_] {A = A} {φ = φ} f g = unglue {_}{_}{A}{φ} g


glue-prop : ∀ {ℓ} {A :{#} Set ℓ} {φ :{#} Prop} {T :{#} Partial (Set ℓ) φ} {f :{¶} PartialP φ (λ o → T o → A)} →
            (t :{¶} PartialP φ T) (a :{¶} A) →
            PartialP φ (λ o → a ¶≡ f o (t o)) →
            Glue⟨ A ← T , f ⟩
glue-prop {φ = φ} {f = f} t a peq = glue⟨ t ↦ ext-subst (λ _ → a) (λ { (φ = p⊤) → f _ (t _) }) (λ { (φ = p⊤) → peq _ }) (cut a) ⟩

postulate
  uip : ∀ {ℓ} {A :{#} Set ℓ} {a b :{#} A} {e e' : a ≡ b} → e ≡ e'

glue-prop-cong : ∀ {ℓ} {A :{#} Set ℓ} {φ :{#} Prop} {T :{#} Partial (Set ℓ) φ} {f :{¶} PartialP φ (λ o → T o → A)} →
                 (t t' :{¶} PartialP φ (λ o → T o)) (t-eq : PartialP φ (λ o → t o ¶≡ t' o)) →
                 (a a' :{¶} A) (a-eq : a ¶≡ a') →
                 (peq :{¶} PartialP φ (λ o → a ¶≡ f o (t o))) (peq' :{¶} PartialP φ (λ o → a' ¶≡ f o (t' o))) →
                 glue-prop {f = f} t a peq ≡ glue-prop t' a' peq'
glue-prop-cong {A = A} {φ} {T} {f} t t' t-eq = ¶subst {A = PartialP φ (λ o → T o)}
                                                      (λ y → (a a' :{¶} A) (a-eq : a ¶≡ a') →
                                                              (peq :{¶} PartialP φ (λ o → a ¶≡ f o (t o))) (peq' :{¶} PartialP φ (λ o → a' ¶≡ f o (y o))) →
                                                              glue-prop {f = f} t a peq ≡ glue-prop y a' peq')
                                                      {x₁ = t} {x₂ = t'}
                                                      (partext-¶eq {A = T} (λ o → t o) (λ o → t' o) t-eq)
                                                      (λ a a' a-eq → ¶subst {A = A}
                                                                             (λ y → (peq :{¶} PartialP φ (λ o → a ¶≡ f o (t o))) (peq' :{¶} PartialP φ (λ o → y ¶≡ f o (t o))) →
                                                                                     glue-prop {f = f} t a peq ≡ glue-prop t y peq')
                                                                             {x₁ = a} {x₂ = a'}
                                                                             a-eq
                                                                             (λ peq peq' → cong {A = PartialP φ (λ o → a ¶≡ f o (t o))} {B = Glue⟨ A ← T , f ⟩} (glue-prop t a) {a = peq} {b = peq'} (irr-funext (λ { o → uip }))))

{-
-- glue-cong using equality of pointwise pairs (meeting Dominique 20/10/19) ...
glue-cong : ∀ {la lb} {A :{#} Set la} {φ :{#} Prop} {T :{#} .(IsOne φ) → Set lb} {f :{¶} .(o : IsOne φ) → T o → A} →
            (p p' : ¶Σ (.(o : IsOne φ) → T o) (λ t → A [ (λ o → f o (t o)) ])) → p ≡ p' →
            glue {f = f} (¶fst p) (paste[ (λ o → f o (¶fst p o)) ] (¶snd p)) ≡ glue (¶fst p') (paste[ (λ o → f o (¶fst p' o)) ] (¶snd p'))
glue-cong {f = f} p p' eq = J eq (λ p' _ → glue {f = f} (¶fst p) (paste[ (λ o → f o (¶fst p o)) ] (¶snd p)) ≡ glue (¶fst p') (paste[ (λ o → f o (¶fst p' o)) ] (¶snd p'))) (refl _)


-- Equality of pointwise pairs (see above) is equivalent to pointwise equality of first components
-- and (parametric) equality of second components (properly transported).
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

-- It is probably unsound to postulate congruence for pointwise functions (see mail Andreas 2/1/20).
postulate
  ¶cong : ∀{ℓA ℓB} {A :{#} Set ℓA} {B :{#} Set ℓB} (f : (a :{¶} A) → B) {a a' :{¶} A} → a ≡ a' → f a ≡ f a'
  
ext-subst' : ∀{ℓ} {A : Set ℓ} {φ : Prop} {pa pa' :{¶} Partial A φ} → pa ≡ pa' → A [ pa ] → A [ pa' ]
ext-subst' {_} {A} {φ} {pa} {pa'} eq exta = subst id (¶cong (λ (y :{¶} Partial A φ) → A [ y ]) eq) exta
-}

-- Building a bridge between two permonads using extension types (without definitional equality
-- constraints for monads or monad morphisms, but using pointwise equalities).

postulate
  ℓ : Level
  A :{#} Set ℓ
  f : (M :{#} Premonad ℓ) → type M A → type M A
  κ1 :{¶} Premonad ℓ
  κ1-mon : IsMonad κ1
  κ2 :{¶} Premonad ℓ
  κ2-mon : IsMonad κ2
  h :{¶} MonadMap κ1 κ2

postulate
  h-return-law : {X :{#} Set ℓ} (x :{¶} X) → h (return κ1 x) ¶≡ return κ2 x
  h-bind-law :{¶} {X Y :{#} Set ℓ} {mx :{¶} type κ1 X} {q :{¶} (x :{¶} X) → type κ1 Y} →
                  h (bind κ1 mx q) ¶≡ bind κ2 (h mx) (h ∘¶ q)


-- Bridge from (type κ1 X) to (type κ2 X)
h-bridge :{#} Set ℓ → 𝕀 → Set ℓ
h-bridge X = / h {X} /

-- Bridge from (type κ1) to (type κ2)
type-op-bridge :{#} 𝕀 → Set ℓ → Set ℓ
type-op-bridge i X = h-bridge X i

-- Bridge in Premonad from κ1 to κ2
pm-bridge :{#} 𝕀 → Premonad ℓ
pm-bridge i = premonad [ type-op-bridge i ,
                       [¶ (λ {X :{#} Set ℓ} x → push (h {X}) i (return κ1 x) ) ,
                       [¶ (λ {X Y :{#} Set ℓ} brx q → glue-prop (λ { ((i ≣ i0) = p⊤) → bind κ1 brx q ;
                                                                      ((i ≣ i1) = p⊤) → bind κ2 brx q })
                                                                 (bind κ2 (pull (h {X}) i brx) ((pull (h {Y}) i) ∘¶ q))
                                                                 (λ { ((i ≣ i0) = p⊤) → ¶sym {a = h (bind κ1 brx q)} {b = bind κ2 (h brx) (h ∘¶ q)} h-bind-law ;
                                                                      ((i ≣ i1) = p⊤) → ¶refl (bind κ2 brx q) })) ,
                       tt ] ] ]

endpoint-0 : pm-bridge i0 ≡ κ1
endpoint-0 = cong (λ x → premonad [ type κ1 ,
                                    [¶ (λ {_ :{#} _} → return κ1) ,
                                    [¶ (λ {_ _ :{#} _} → bind κ1) ,
                                    x ] ] ])
                   (unique-⊤ tt (trivial κ1))

-- Is this sound?
postulate
  funext-¶eq : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} →
               {f g :{¶} (a : A) → B a} →
               ((a :{¶} A) → f a ¶≡ g a) → f ¶≡ g
  #funext-¶eq : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} →
                {f g :{¶} (a :{#} A) → B a} →
                ((a :{#} A) → f a ¶≡ g a) → f ¶≡ g
  #funext-implicit-¶eq : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} →
                          {f g :{¶} {a :{#} A} → B a} →
                          ({a :{#} A} → f {a} ¶≡ g {a}) → (λ {x :{#} _} → f {x}) ¶≡ (λ {x :{#} _} → g {x})

endpoint-1 : pm-bridge i1 ≡ κ2
endpoint-1 = ¶≡-to-≡ _ _ (¶cong (λ x → premonad [ type κ2 , [¶ x , [¶ (λ {_ _ :{#} _} → bind κ2) , tt ] ] ])
                                {a = λ {X :{#} _} x → h (return κ1 x)} {b = λ {X :{#} _} x → return κ2 x}
                                (#funext-implicit-¶eq {f = λ {X :{#} _} x → h (return κ1 x)} {g = λ {X :{#} _} x → return κ2 x}
                                                      (λ {_ :{#} _} → funext-¶eq {f = λ x → h (return κ1 x)} {g = λ x → return κ2 x} h-return-law)))
             •
             cong (λ x → premonad [ type κ2 ,
                                   [¶ (λ {_ :{#} _} → return κ2) ,
                                   [¶ (λ {_ _ :{#} _} → bind κ2) ,
                                   x ] ] ])
                  (unique-⊤ tt (trivial κ2))

_≡⟨_⟩_ : ∀ {ℓ} {X :{#} Set ℓ} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p • q

_∎ : ∀ {ℓ} {X :{#} Set ℓ} (x : X) → x ≡ x
x ∎ = refl x

infixr 25 _≡⟨_⟩_


monad-law-br1 : (i : 𝕀) (X Y :{#} Set ℓ) (x :{¶} X) (q :{¶} (x :{¶} X) → type (pm-bridge i) Y) → bind (pm-bridge i) (return (pm-bridge i) x) q ≡ q x
monad-law-br1 i X Y x q = bind (pm-bridge i) (return (pm-bridge i) x) q
  ≡⟨ refl _ ⟩ glue-prop (λ { ((i ≣ i0) = p⊤) → bind κ1 (return κ1 x) q ;
                             ((i ≣ i1) = p⊤) → bind κ2 (h (return κ1 x)) q })
                       (bind κ2 (h (return κ1 x)) ((pull (h {Y}) i) ∘¶ q))
                       (λ { ((i ≣ i0) = p⊤) → ¶sym {a = h (bind κ1 (return κ1 x) q)} {b = bind κ2 (h (return κ1 x)) (h ∘¶ q)} h-bind-law ;
                            ((i ≣ i1) = p⊤) → ¶refl (bind κ2 (h (return κ1 x)) q) })
  ≡⟨ ¶J-app (h (return κ1 x)) (return κ2 x) (h-return-law x)
            (λ y w → glue-prop (λ { ((i ≣ i0) = p⊤) → bind κ1 (return κ1 x) q ;
                                     ((i ≣ i1) = p⊤) → bind κ2 y q })
                                (bind κ2 y ((pull (h {Y}) i) ∘¶ q))
                                (λ { ((i ≣ i0) = p⊤) → ¶trans {a = bind κ2 y (h ∘¶ q)}
                                                               {b = bind κ2 (h (return κ1 x)) (h ∘¶ q)}
                                                               {c = h (bind κ1 (return κ1 x) q)}
                                                               (¶cong (λ (z :{¶} _) → bind κ2 z (h ∘¶ q)) (¶sym {a = h (return κ1 x)} {b = y} w))
                                                               (¶sym {a = h (bind κ1 (return κ1 x) q)} {b = bind κ2 (h (return κ1 x)) (h ∘¶ q)} h-bind-law) ;
                                     ((i ≣ i1) = p⊤) → ¶refl (bind κ2 y q) })) ⟩
    glue-prop (λ { ((i ≣ i0) = p⊤) → bind κ1 (return κ1 x) q ;
                    ((i ≣ i1) = p⊤) → bind κ2 (return κ2 x) q })
              (bind κ2 (return κ2 x) ((pull (h {Y}) i) ∘¶ q))
              (λ { ((i ≣ i0) = p⊤) → ¶trans {a = bind κ2 (return κ2 x) (h ∘¶ q)}
                                             {b = bind κ2 (h (return κ1 x)) (h ∘¶ q)}
                                             {c = h (bind κ1 (return κ1 x) q)}
                                             (¶cong (λ (z :{¶} _) → bind κ2 z (h ∘¶ q)) (¶sym {a = h (return κ1 x)} {b = return κ2 x} (h-return-law x)))
                                             (¶sym {a = h (bind κ1 (return κ1 x) q)} {b = bind κ2 (h (return κ1 x)) (h ∘¶ q)} h-bind-law) ;
                   ((i ≣ i1) = p⊤) → ¶refl (bind κ2 (return κ2 x) q) })
  ≡⟨ glue-prop-cong (λ { ((i ≣ i0) = p⊤) → bind κ1 (return κ1 x) q ;
                         ((i ≣ i1) = p⊤) → bind κ2 (return κ2 x) q })
                    (λ { ((i ≣ i0) = p⊤) → q x ; ((i ≣ i1) = p⊤) → q x })
                    (λ { ((i ≣ i0) = p⊤) → return-law1 κ1-mon ; ((i ≣ i1) = p⊤) → return-law1 κ2-mon })
                    (bind κ2 (return κ2 x) ((pull (h {Y}) i) ∘¶ q))
                    (unglue[ (λ { ((i ≣ i0) = p⊤) → h {Y} ; ((i ≣ i1) = p⊤) → id }) ] (q x))
                    (return-law1 κ2-mon)
                    (λ { ((i ≣ i0) = p⊤) → ¶trans {a = bind κ2 (return κ2 x) (h ∘¶ q)}
                                             {b = bind κ2 (h (return κ1 x)) (h ∘¶ q)}
                                             {c = h (bind κ1 (return κ1 x) q)}
                                             (¶cong (λ (z :{¶} _) → bind κ2 z (h ∘¶ q)) (¶sym {a = h (return κ1 x)} {b = return κ2 x} (h-return-law x)))
                                             (¶sym {a = h (bind κ1 (return κ1 x) q)} {b = bind κ2 (h (return κ1 x)) (h ∘¶ q)} h-bind-law) ;
                         ((i ≣ i1) = p⊤) → ¶refl (bind κ2 (return κ2 x) q) })
                    (λ { ((i ≣ i0) = p⊤) → ¶refl (h (q x)) ; ((i ≣ i1) = p⊤) → ¶refl (q x) }) ⟩
    glue-prop (λ { ((i ≣ i0) = p⊤) → q x ;
                   ((i ≣ i1) = p⊤) → q x })
              (unglue[ (λ { ((i ≣ i0) = p⊤) → h {Y} ; ((i ≣ i1) = p⊤) → id }) ] (q x))
              (λ { ((i ≣ i0) = p⊤) → ¶refl (h (q x)) ; ((i ≣ i1) = p⊤) → ¶refl (q x) })
  ≡⟨ {!refl (q x)!} ⟩ (q x ∎)
