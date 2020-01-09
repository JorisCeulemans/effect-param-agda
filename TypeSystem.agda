{-# OPTIONS --cubical --rewriting #-}

module TypeSystem where
open import Primitives public
open import Agda.Primitive hiding (i0 ; i1) public


Π : ∀{ℓA ℓB} (A : Set ℓA) → (B : A → Set ℓB) → Set (ℓB ⊔ ℓA)
Π A B = (a : A) → B a
hΠ : ∀{ℓA ℓB} (A : Set ℓA) → (B : A → Set ℓB) → Set (ℓB ⊔ ℓA)
hΠ A B = {a : A} → B a

---------------------------------
-- Identity type --
---------------------------------

postulate
  _≡_ : ∀{ℓ} {A : Set ℓ} (a b : A) → Set ℓ
  refl : ∀{ℓ} {A :{#} Set ℓ} (a :{#} A) → a ≡ a
  J : ∀{ℓA ℓC} {A :{#} Set ℓA} {a b :{#} A} (e : a ≡ b) (C :{#} (y : A) → (w : a ≡ y) → Set ℓC) (c : C a (refl a))
    → C b e
  rw-Jβ : ∀{ℓA ℓC} →
      {A :{#} Set ℓA} →
      {a :{#} A} →
      (C :{#} (y : A) → (w : a ≡ y) → Set ℓC) →
      (c : C a (refl a)) →
      J (refl a) C c ≡ c

infix 1 _≡_

{-# BUILTIN REWRITE _≡_ #-}

{-# REWRITE rw-Jβ #-}

-- postulate
--  funext : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : Π A B} → ((x : A) → f x ≡ g x) → f ≡ g

-------------------------------------------
-- Σ-types --
-------------------------------------------

postulate
  Σ #Σ : ∀{ℓA ℓB} → (A : Set ℓA) → (B : A → Set ℓB) → Set (ℓB ⊔ ℓA)
  ¶Σ : ∀{ℓA ℓB} → (A : Set ℓA) → (B : (_ :{¶} A) → Set ℓB) → Set (ℓB ⊔ ℓA)

-- Continuous Σ-type --
-----------------------

postulate
  [_,_] : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (a : A) → (b : B a) → Σ A B
  fst : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → Σ A B → A
  snd : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (p : Σ A B) → B (fst p)
  rw-fst : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (a : A) → (b : B a)
    → fst ([_,_] {_}{_}{A}{B} a b) ≡ a
{-# REWRITE rw-fst #-}
postulate
  rw-snd : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (a : A) → (b : B a)
    → snd ([_,_] {_}{_}{A}{B} a b) ≡ b
  rw-fst,snd : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (p : Σ A B)
    → [_,_] {_}{_}{A}{B} (fst p) (snd p) ≡ p
{-# REWRITE rw-snd #-}
{-# REWRITE rw-fst,snd #-}

--An induction principle is definable in terms of fst and snd. We give only the continuous induction pr'ple
split : ∀{ℓA ℓB ℓC} → h#Π (Set ℓA) λ A → h#Π (A → Set ℓB) λ B
    → Π (Σ A B) λ p
    → #Π (Σ A B → Set ℓC) λ C
    → Π (Π A λ a → Π (B a) λ b → C [ a , b ]) λ c
    → C p
split {_}{_}{_} {A}{B} p C c = c (fst p) (snd p)

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (B : A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀{ℓA ℓB} → (A : Set ℓA) → (B : Set ℓB) → Set (ℓA ⊔ ℓB)
A × B = Σ[ _ ∈ A ] B

#uncurry : ∀ {a b c} → {A :{#} Set a} →  {B :{#} A → Set b} →
                       {C :{#} Σ A B → Set c} →
                       ((x : A) (y : B x) → C [ x , y ]) → (p : Σ A B) → C p
#uncurry f p = f (fst p) (snd p)

-- Parametric Σ-type (∃) --
---------------------------

--We should additionally postulate pointwise and parametric induction principles, but we only include the continuous one.
postulate
  [#_,_] : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → #Π A λ a → (b : B a) → #Σ A B
  #split : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB}
    → (p : #Σ A B)
    → (C :{#} #Σ A B → Set ℓC)
    → (c : (a :{#} A) → (b : B a) → C [# a , b ])
    → C p
  rw-#Σ-β : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB}
    → (a :{#} A) → (b : B a)
    → (C :{#} #Σ A B → Set ℓC)
    → (c : (a :{#} A) → (b : B a) → C [# a , b ])
    → #split [# a , b ] C c ≡ c a b
{-# REWRITE rw-#Σ-β #-}

infix 2 #Σ-syntax

#Σ-syntax : ∀ {a b} (A : Set a) → (B : A → Set b) → Set (a ⊔ b)
#Σ-syntax = #Σ

syntax #Σ-syntax A (λ x → B) = #Σ[ x ∈ A ] B

uncurry# : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB}
  → {C :{#} #Σ A B → Set ℓC}
  → (c : (a :{#} A) → (b : B a) → C [# a , b ])
  → (p : #Σ A B)
  → C p
uncurry# {C = C} c p = #split p C c


-- Pointwise Σ-type --
----------------------

--We should additionally postulate pointwise and parametric induction principles, but we only include the continuous one.
--With the parametric induction principle, we could define ¶fst and ¶snd
postulate
  [¶_,_] : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} → (a :{¶} A) → (b : B a) → ¶Σ A B
  ¶fst : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} → (_ :{#} ¶Σ A B) → A
  ¶snd : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} → (p : ¶Σ A B) → B (¶fst p)
  rw-¶fst : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} → (a :{¶} A) → (b : B a)
            → ¶fst ([¶_,_] {_}{_}{A}{B} a b) ≡ a
{-# REWRITE rw-¶fst #-}

postulate
  rw-¶snd : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} → (a :{¶} A) → (b : B a)
            → ¶snd ([¶_,_] {_}{_}{A}{B} a b) ≡ b
  rw-¶fst,¶snd : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (p : ¶Σ A B)
                 → [¶_,_] {_}{_}{A}{B} (¶fst p) (¶snd p) ≡ p
{-# REWRITE rw-¶snd #-}
{-# REWRITE rw-¶fst,¶snd #-}

¶split : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB}
  → (p : ¶Σ A B)
  → (C :{#} ¶Σ A B → Set ℓC)
  → (c : (a :{¶} A) → (b : B a) → C [¶ a , b ])
  → C p
¶split p C c = c (¶fst p) (¶snd p)

rw-¶Σ-β : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB}
  → (a :{¶} A) → (b : B a)
  → (C :{#} ¶Σ A B → Set ℓC)
  → (c : (a :{¶} A) → (b : B a) → C [¶ a , b ])
  → ¶split [¶ a , b ] C c ≡ c a b
rw-¶Σ-β a b C c = refl _

¶split# : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB}
  → (p :{#} ¶Σ A B)
  → (C :{#} (s :{#} ¶Σ A B) → Set ℓC)
  → (c : (a :{¶} A) → (b :{#} B a) → C [¶ a , b ])
  → C p
¶split# p C c = c (¶fst p) (¶snd p)

rw-¶Σ-β# : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB}
  → (a :{¶} A) → (b :{#} B a)
  → (C :{#} (s :{#} ¶Σ A B) → Set ℓC)
  → (c : (a :{¶} A) → (b :{#} B a) → C [¶ a , b ])
  → ¶split# [¶ a , b ] C c ≡ c a b
rw-¶Σ-β# a b C c = refl _

{-¶fst : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} → (_ :{#} ¶Σ A B) → A
¶fst {_}{_}{A}{B} p = ¶split# p (λ _ → A) (λ a b → a)

¶snd : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} → (p : ¶Σ A B) → B (¶fst p)
¶snd {_}{_}{A}{B} p = ¶split p (λ p → B (¶fst p)) (λ a b → b)
-}
--¶snd : ∀{ℓA ℓB} → h#Π (Set ℓA) λ A → h#Π ((_ :{¶} A) → Set ℓB) λ B → (p : ¶Σ A B) → B (¶fst p)
--¶snd {_}{_}{A}{B} p = ¶split p (λ p → B (¶fst p)) (λ a b → b)

infix 2 ¶Σ-syntax

¶Σ-syntax : ∀ {a b} (A : Set a) → (B : (_ :{¶} A) → Set b) → Set (a ⊔ b)
¶Σ-syntax = ¶Σ

syntax ¶Σ-syntax A (λ x → B) = ¶Σ[ x ∈ A ] B

-------------------------------------------
-- Glueing and Welding --
-------------------------------------------

Glue : ∀{ℓ} (A : Set ℓ) → ∀ φ → (T : Partial (Set ℓ) φ) → (f :{¶} PartialP φ (λ o → T o → A)) → Set ℓ
Glue A φ T f = primGlue A φ T f

module Welding where
  primitive
    primCoGlue : _
    prim^coglue : _ {- {la lb : Level} {A : Set la} #{φ : Prop}
                    {T : .(o : IsOne φ) → Set lb} ¶{f : .(o : IsOne φ) → A → T o} →
                    A → primCoGlue A φ T f -}
    prim^mcoglue : _ {- {la lb lc : Level} #{A : Set la} #{φ : Prop}
                     #{T : .(o : IsOne φ) → Set lb} ¶{f : .(o : IsOne φ) → A → T o}
                     #{C : primCoGlue A φ T f → Set lc}
                     (c0 : (a : A) → C (prim^coglue a))
                     (c : .(o : IsOne φ) (t : T o) → C t) (b : primCoGlue A φ T f) →
                     C b -}
open Welding public renaming (primCoGlue to Weld ; prim^coglue to weld ; prim^mcoglue to mweld)

--Weld : ∀{ℓ} (A : Set ℓ) → ∀ φ → (T : Partial (Set ℓ) φ) → ¶Π (PartialP φ (λ o → A → T o)) λ f → Set ℓ
--Weld A φ T f = primWeld A φ T f

-------------------------------------------
-- PATH DEGENERACY AXIOM --
-------------------------------------------

postulate
  pathDisc : ∀{ℓ} → {A :{#} Set ℓ} → (p :{#} (_ :{#} 𝕀) → A) → p ≡ (λ _ → p b0)

-------------------------------------------
-- AUXILIARY STUFF --
-------------------------------------------

-- FUNCTIONS

id : ∀{ℓ} {A :{#} Set ℓ} → A → A
id a = a

_∘_ : ∀{ℓA ℓB ℓC} →
    {A :{#} Set ℓA} →
    {B :{#} Set ℓB} →
    {C :{#} B → Set ℓC} →
    (g : (b : B) → C b) →
    (f : A → B) →
    ((a : A) → C (f a))
_∘_ {ℓA}{ℓB}{ℓC}{A}{B}{C} g f a = g (f a)

_∘¶_ : ∀{ℓA ℓB ℓC} {A :{#} Set ℓA} {B :{#} Set ℓB} {C :{#} B → Set ℓC} →
       (g : (b : B) → C b) →
       (f : (a :{¶} A) → B) →
       ((a :{¶} A) → C (f a))
_∘¶_ g f a = g (f a)

infixr 20 _∘_
infixr 20 _∘¶_

-- FUNCTION EXTENSIONALITY

postulate
  funext : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} →
           {f g :{#} (a : A) → B a} →
           ((a : A) → f a ≡ g a) → f ≡ g
  #funext : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} →
           {f g :{#} (a :{#} A) → B a} →
           ((a :{#} A) → f a ≡ g a) → f ≡ g
  ¶funext : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} →
           {f g :{#} (a :{¶} A) → B a} →
           ((a :{¶} A) → f a ≡ g a) → f ≡ g

-- EQUALITY

subst : ∀ {a p} → {A :{#} Set a} → (P :{#} A → Set p) →
         {x₁ :{#} _} → {x₂ :{#} _} → x₁ ≡ x₂ → P x₁ → P x₂
subst P eq p = J eq (\ y _ → P y) p

sym : ∀{ℓ} →
      {A :{#} Set ℓ} →
      {a b :{#} A} →
      b ≡ a → a ≡ b
sym {ℓ}{A}{a}{b} e = J e (λ y w → y ≡ b) (refl b)

trans : ∀ {a} → {A :{#} Set a} → {x y z :{#} A} →
                x ≡ y → y ≡ z → x ≡ z
trans p q = subst (\ x → _ ≡ x) q p

_•_ = trans
infixl 0 _•_

cong : ∀{ℓA ℓB} →
      {A :{#} Set ℓA} →
      {B :{#} Set ℓB} →
      (f :{#} A → B) →
      {a b :{#} A} →
      (a ≡ b) → (f a ≡ f b)
cong {ℓA}{ℓB}{A}{B} f {a}{b} e = J e (λ y w → f a ≡ f y) (refl (f a))

cong-app : ∀{ℓA ℓB} →
      {A :{#} Set ℓA} →
      {B :{#} A → Set ℓB} →
      {f g :{#} (a : A) → B a} →
      (f ≡ g) →
      (a :{#} A) →
      f a ≡ g a
cong-app {ℓA}{ℓB}{A}{B}{f}{g} e a = J e (λ h w → f a ≡ h a) (refl (f a))

#cong-app : ∀{ℓA ℓB} →
      {A :{#} Set ℓA} →
      {B :{#} A → Set ℓB} →
      {f g :{#} (a :{#} A) → B a} →
      (f ≡ g) →
      (a :{#} A) →
      f a ≡ g a
#cong-app {ℓA}{ℓB}{A}{B}{f}{g} e a = J e (λ h w → f a ≡ h a) (refl (f a))


-- ANNOTATION

_∋_ : ∀{ℓ} → (A :{#} Set ℓ) → A → A
A ∋ a = a

-- PATH DEGENERACY

path-to-eq : ∀{ℓ} → {A :{#} Set ℓ} → (p :{#} (_ :{#} 𝕀) → A) → p i0 ≡ p i1
path-to-eq p = sym (#cong-app (pathDisc p) i1)


---------------------------------
-- Lifting --
---------------------------------
postulate
  Lift : ∀{ℓ} ℓ' → Set ℓ → Set (ℓ ⊔ ℓ')
  lift : ∀{ℓ} ℓ' → {A :{#} Set ℓ} → A → Lift ℓ' A
  lower : ∀{ℓ} ℓ' → {A :{#} Set ℓ} → Lift ℓ' A → A
  rw-lift-β : ∀{ℓ} ℓ' → {A :{#} Set ℓ} → (a : A) → lower ℓ' (lift ℓ' a) ≡ a
  rw-lift-η : ∀{ℓ} ℓ' → {A :{#} Set ℓ} → (a : Lift ℓ' A) → lift ℓ' (lower ℓ' a) ≡ a
{-# REWRITE rw-lift-β #-}
{-# REWRITE rw-lift-η #-}

---------------
-- Booleans
---------------

postulate
 Bool : Set
 true false : Bool
 bool : ∀ {a} {A :{ # } Bool → Set a} → A true → A false → ∀ b → A b
 bool-rw1 : ∀ {a} {A :{ # } Bool → Set a} → (t : A true) → (f : A false) → bool {A = A} t f true ≡ t
 bool-rw2 : ∀ {a} {A :{ # } Bool → Set a} → (t : A true) → (f : A false) → bool {A = A} t f false ≡ f
 bool# : ∀ {a} {A :{ # } Bool → Set a} → A true → A false → (b :{#} Bool) → A b
 bool#-rw1 : ∀ {a} {A :{ # } Bool → Set a} → (t : A true) → (f : A false) → bool# {A = A} t f true ≡ t
 bool#-rw2 : ∀ {a} {A :{ # } Bool → Set a} → (t : A true) → (f : A false) → bool# {A = A} t f false ≡ f
 bool¶ : ∀ {a} {A :{ # } (_ :{¶} Bool) → Set a} → A true → A false → (b :{¶} Bool) → A b
 bool¶-rw1 : ∀ {a} {A :{ # } (_ :{¶} Bool) → Set a} → (t : A true) → (f : A false) → bool¶ {A = A} t f true ≡ t
 bool¶-rw2 : ∀ {a} {A :{ # } (_ :{¶} Bool) → Set a} → (t : A true) → (f : A false) → bool¶ {A = A} t f false ≡ f

{-# REWRITE bool-rw1 bool-rw2 #-}
{-# REWRITE bool#-rw1 bool#-rw2 #-}
{-# REWRITE bool¶-rw1 bool¶-rw2 #-}

infix  0 if_then_else_
if_then_else_ : ∀ {a} {A :{#} Set a} → Bool → A → A → A
if_then_else_ b t f = bool t f b

infix 0 ifp_thenp_elsep_
ifp_thenp_elsep_ : ∀ {a} {A :{#} Bool → Set a} → (b : Bool) → ((b ≡ true) → A true) → ((b ≡ false) → A false) → A b
ifp_thenp_elsep_ = bool (λ tr fa → tr (refl true)) (λ tr fa → fa (refl false))


_+_ : ∀{ℓA ℓB} → Set ℓA → Set ℓB → Set (ℓA ⊔ ℓB)
_+_ {ℓA} {ℓB} A B = Σ Bool \ b → if b then Lift ℓB A else Lift ℓA B

inl : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} Set ℓB} → A → A + B
inl a = [ true , lift _ a ]

inr : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} Set ℓB} → B → A + B
inr b = [ false , lift _ b ]

+-elim : ∀ {ℓA ℓB ℓC} {A :{#} Set ℓA} {B :{#} Set ℓB}
         (C :{#} A + B → Set ℓC)
         (left : (a : A) → C (inl a))
         (right : (b : B) → C (inr b))
         (x : A + B) → C x
+-elim {ℓA} {ℓB} {ℓC} {A} {B} C left right x = bool {A = λ b → (s : if b then Lift ℓB A else Lift ℓA B) → C [ b , s ]} (left ∘ lower _) (right ∘ lower _) (fst x) (snd x)

+-elim# : ∀ {ℓA ℓB ℓC} {A :{#} Set ℓA} {B :{#} Set ℓB}
          (C :{#} A + B → Set ℓC)
          (left : (a :{#} A) → C (inl a))
          (right : (b :{#} B) → C (inr b))
          (x :{#} A + B) → C x
+-elim# {ℓA}{ℓB}{ℓC}{A}{B} C left right x = bool# {A = λ b → (s :{#} if b then Lift ℓB A else Lift ℓA B) → C [ b , s ]} (λ y → left (lower _ y)) (λ y → right (lower _ y)) (fst x) (snd x)

+-elim¶ : {ℓA ℓB ℓC :{¶} _} {A :{#} Set ℓA} {B :{#} Set ℓB}
          (C :{#} (_ :{¶} A + B) → Set ℓC)
          (left : (a :{¶} A) → C (inl a))
          (right : (b :{¶} B) → C (inr b))
          (x :{¶} A + B) → C x
+-elim¶ {ℓA}{ℓB}{ℓC}{A}{B} C left right x = bool¶ {A = λ b → (s :{¶} if b then Lift ℓB A else Lift ℓA B) → C [ b , s ]} (λ s → left (lower _ s)) (λ s → right (lower _ s)) (fst x) (snd x)

---------------
-- Unit
---------------

postulate
  ⊤ : Set
  tt : ⊤
  unit : ∀ {a} {A :{ # } ⊤ → Set a} → A tt → ∀ b → A b
  unit-rw : ∀ {a} {A :{ # } ⊤ → Set a} → (t : A tt) → unit {A = A} t tt ≡ t
  unit# : ∀ {a} {A :{ # } ⊤ → Set a} → A tt → (b :{#} ⊤) → A b
  unit#-rw : ∀ {a} {A :{ # } ⊤ → Set a} → (t : A tt) → unit# {A = A} t tt ≡ t
  unit¶ : ∀ {a} {A :{ # } (_ :{¶} ⊤) → Set a} → A tt → (b :{¶} ⊤) → A b
  unit¶-rw : ∀ {a} {A :{ # } (_ :{¶} ⊤) → Set a} → (t : A tt) → unit¶ {A = A} t tt ≡ t

{-# REWRITE unit-rw unit#-rw unit¶-rw #-}

unique-⊤ : (x y :{#} ⊤) → x ≡ y
unique-⊤ x y = unit# {A = λ t → t ≡ y} (unit# {A = λ t' → tt ≡ t'} (refl tt) y) x

---------------------------------
-- Pointwise equality --
---------------------------------
_¶≡_ : ∀ {ℓ} {A : Set ℓ} (a b :{¶} A) → Set ℓ
a ¶≡ b = [¶ a , tt ] ≡ [¶ b , tt ]

¶refl : ∀ {ℓ} {A :{#} Set ℓ} (a :{¶} A) → a ¶≡ a
¶refl a = refl [¶ a , tt ]

¶≡-to-≡ : ∀ {ℓ} {A :{#} Set ℓ} (a b :{¶} A) → a ¶≡ b → a ≡ b
¶≡-to-≡ a b e = cong ¶fst e

eta-¶Box : ∀ {ℓ} {A :{#} Set ℓ} (p : ¶Σ A (λ _ → ⊤)) → p ≡ [¶ ¶fst p , tt ]
eta-¶Box p = cong (λ x → [¶ ¶fst p , x ]) (unique-⊤ (¶snd p) tt)

¶J : ∀ {ℓA ℓC} {A :{#} Set ℓA} (a b :{¶} A) (e : a ¶≡ b) (C :{#} (y :{¶} A) → (w : a ¶≡ y) → Set ℓC) (c : C a (¶refl a))
   → C b e
¶J a b e C c = J e (λ y w → C (¶fst y) (w • eta-¶Box y)) c

¶subst : ∀ {a p} → {A :{#} Set a} → (P :{#} (_ :{¶} A) → Set p) →
         {x₁ x₂ :{¶} A} → x₁ ¶≡ x₂ → P x₁ → P x₂
¶subst P {x₁} {x₂} eq p = ¶J x₁ x₂ eq (λ y _ → P y) p

¶sym : ∀ {ℓ} {A :{#} Set ℓ} {a b :{¶} A} → a ¶≡ b → b ¶≡ a
¶sym {a = a} {b} e = ¶J a b e (λ y _ → y ¶≡ a) (¶refl a)

¶trans : ∀ {ℓ} {A :{#} Set ℓ} {a b c :{¶} A} → a ¶≡ b → b ¶≡ c → a ¶≡ c
¶trans {a = a} {b} {c} p q = ¶J b a (¶sym {a = a} {b} p) (λ y _ → y ¶≡ c) q

¶cong : ∀ {ℓA ℓB} →
        {A :{#} Set ℓA} →
        {B :{#} Set ℓB} →
        (f :{¶} (_ :{¶} A) → B) →
        {a b :{¶} A} →
        (a ¶≡ b) → (f a ¶≡ f b)
¶cong {ℓA}{ℓB}{A}{B} f {a}{b} e = ¶J a b e (λ y w → f a ¶≡ f y) (¶refl (f a))

¶J-app-¶eq : ∀ {ℓA ℓC} {A :{#} Set ℓA} {C :{#} Set ℓC} (a b :{¶} A) (e :{¶} a ¶≡ b)
             (f :{¶} (y :{¶} A) → (w :{#} a ¶≡ y) → C) →
             f a (¶refl a) ¶≡ f b e
¶J-app-¶eq a b e f = ¶J a b e (λ y w → f a (¶refl a) ¶≡ f y w) (¶refl (f a (¶refl a)))

¶J-app : ∀ {ℓA ℓC} {A :{#} Set ℓA} {C :{#} Set ℓC} (a b :{¶} A) (e : a ¶≡ b)
         (f : (y :{¶} A) → (w : a ¶≡ y) → C) →
         f a (¶refl a) ≡ f b e
¶J-app a b e f = ¶J a b e (λ y w → f a (¶refl a) ≡ f y w) (refl _)

unique-⊤-¶eq : (x y :{¶} ⊤) → x ¶≡ y
unique-⊤-¶eq x y = unit¶ {A = λ t → t ¶≡ y} (unit¶ {A = λ t' → tt ¶≡ t'} (¶refl tt) y) x


---------------
-- Numbers
---------------

postulate
  Nat : Set
  zero : Nat
  succ : Nat → Nat
  nat : ∀ {ℓ} {A :{#} Nat → Set ℓ}
          → (z : A zero)
          → (s : (n : Nat) → A n → A (succ n))
          → (n : Nat)
          → A n
  nat-rw0 : ∀ {ℓ} {A :{#} Nat → Set ℓ}
              → (z : A zero)
              → (s : (n : Nat) → A n → A (succ n))
              → nat z s zero ≡ z
  nat-rws : ∀ {ℓ} {A :{#} Nat → Set ℓ}
              → (z : A zero)
              → (s : (n : Nat) → A n → A (succ n))
              → (n : Nat)
              → nat z s (succ n) ≡ s n (nat z s n)

{-# REWRITE nat-rw0 #-}
{-# REWRITE nat-rws #-}

_+Nat_ : Nat → Nat → Nat
_+Nat_ m n = nat n (λ _ r → succ r) m

is-zero : Nat → Bool
is-zero n = nat true (λ _ _ → false) n

pred : Nat → Nat
pred n = nat zero (λ n' _ → n') n

_-Nat_ : Nat → Nat → Nat
_-Nat_ m n = nat m (λ _ r → pred r) n

_≤Nat_ : Nat → Nat → Bool
_≤Nat_ m n = is-zero (m -Nat n)

---------------
-- Lists
---------------

postulate
  List : ∀ {ℓ} → Set ℓ → Set ℓ
  [] : ∀ {ℓ} {A :{#} Set ℓ} → List A
  _::_ : ∀ {ℓ} {A :{#} Set ℓ} → A → List A → List A
  list : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} List A → Set ℓB}
           → (empty : B [])
           → (cons : (a : A) → (l : List A) → (p : B l) → B (a :: l))
           → (l : List A)
           → B l
  list-rw[] : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} List A → Set ℓB}
                → (empty : B [])
                → (cons : (a : A) → (l : List A) → (p : B l) → B (a :: l))
                → list empty cons [] ≡ empty
  list-rw:: : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} List A → Set ℓB}
                → (empty : B [])
                → (cons : (a : A) → (l : List A) → (p : B l) → B (a :: l))
                → (a : A) → (l : List A)
                → list empty cons (a :: l) ≡ cons a l (list empty cons l)

{-# REWRITE list-rw[] #-}
{-# REWRITE list-rw:: #-}

length : ∀ {ℓ} {A :{#} Set ℓ} → List A → Nat
length l = list zero (λ _ _ r → succ r) l

map : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} Set ℓB} → (A → B) → List A → List B
map f l = list [] (λ a _ map-as → f a :: map-as) l

concat : ∀ {ℓ} {A :{#} Set ℓ} → List (List A) → List A
concat ll = list [] (λ lh _ concat-lt → list concat-lt (λ h _ concat-t → h :: concat-t) lh) ll

append : ∀ {ℓ} {A :{#} Set ℓ} → List A → A → List A
append l a = list (a :: []) ((λ lh _ append-a-lt → lh :: append-a-lt)) l

reverse : ∀ {ℓ} {A :{#} Set ℓ} → List A → List A
reverse l = list [] ((λ h _ rev-t → append rev-t h)) l

sum : List Nat → Nat
sum l = list zero (λ n _ s → n +Nat s) l

---------------
-- Maybe
---------------

Maybe : ∀ {ℓ} → Set ℓ → Set ℓ
Maybe A = ⊤ + A

just : ∀ {ℓ} {A :{#} Set ℓ} → A → Maybe A
just a = inr a

nothing : ∀ {ℓ} {A :{#} Set ℓ} → Maybe A
nothing = inl tt

maybe : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} Maybe A → Set ℓB}
        → (jst : (a : A) → B (just a))
        → (ntg : B nothing)
        → (ma : Maybe A)
        → B ma
maybe {B = B} jst ntg ma = +-elim B (λ x → subst (λ y → B (inl y)) (unique-⊤ tt x) ntg) jst ma

maybe# : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} Maybe A → Set ℓB}
         → (jst : (a :{#} A) → B (just a))
         → (ntg : B nothing)
         → (ma :{#} Maybe A)
         → B ma
maybe# {B = B} jst ntg ma = +-elim# B (λ x → subst (λ y → B (inl y)) (unique-⊤ tt x) ntg) jst ma

maybe¶ : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} (_ :{¶} Maybe A) → Set ℓB}
         → (jst : (a :{¶} A) → B (just a))
         → (ntg : B nothing)
         → (ma :{¶} Maybe A)
         → B ma
maybe¶ {B = B} jst ntg ma = +-elim¶ B (λ x → ¶subst (λ y → B (inl y)) {tt} {x} (unique-⊤-¶eq tt x) ntg) jst ma

mb-map : ∀ {ℓA ℓB} {A :{#} Set ℓA} {B :{#} Set ℓB} → (A → B) → Maybe A → Maybe B
mb-map f ma = maybe (λ a → just (f a)) nothing ma
