{-# OPTIONS --cubical --rewriting #-}

module PointwiseEquality where

open import TypeSystem

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
¶trans {a = a} {b} {c} p q = ¶J b c q (λ y _ → a ¶≡ y) p

¶cong : ∀ {ℓA ℓB} →
        {A :{#} Set ℓA} →
        {B :{#} Set ℓB} →
        (f :{¶} (_ :{¶} A) → B) →
        {a b :{¶} A} →
        (a ¶≡ b) → (f a ¶≡ f b)
¶cong {ℓA}{ℓB}{A}{B} f {a}{b} e = ¶J a b e (λ y w → f a ¶≡ f y) (¶refl (f a))
