{-# OPTIONS --cubical --rewriting #-}
module Monads.Monads where

open import TypeSystem
open import Functors

record Premonad (ℓ : Level) : Set (lsuc ℓ) where
  constructor premonad
  field
    unpremonad : Σ[ F ∈ (Set ℓ → Set ℓ) ] (
                 ¶Σ[ return ∈ ({X :{#} Set ℓ} → X → F X) ] (
                 ¶Σ[ bind ∈ ({X Y :{#} Set ℓ} → F X → (X → F Y) → F Y) ] (
                 ⊤ ) ) )

open Premonad public

type : ∀ {ℓ} → Premonad ℓ → Set ℓ → Set ℓ
type M = fst(unpremonad M)

return : ∀ {ℓ} (M :{#} Premonad ℓ) → {X :{#} Set ℓ} → X → type M X
return M = ¶fst(snd(unpremonad M))

bind : ∀ {ℓ} (M :{#} Premonad ℓ) → {X Y :{#} Set ℓ} → type M X → (X → type M Y) → type M Y
bind M = ¶fst(¶snd(snd(unpremonad M)))

trivial : ∀ {ℓ} (M : Premonad ℓ) → ⊤
trivial M = ¶snd(¶snd(snd(unpremonad M)))

premonad-⊤-irrelevant : ∀ {ℓ} (M : Premonad ℓ) (x : ⊤)
                          → premonad [ type M ,
                                      [¶ (λ {X :{#} Set ℓ} → return M {X}) ,
                                      [¶ (λ {X Y :{#} Set ℓ} → bind M {X} {Y}) ,
                                      x ] ] ]
                             ≡ M
premonad-⊤-irrelevant M x = cong (λ y → premonad [ type M ,
                                                  [¶ (λ {X :{#} Set _} → return M {X}) ,
                                                  [¶ (λ {X Y :{#} Set _} → bind M {X} {Y}) , y ] ] ])
                                 (unique-⊤ x (¶snd (¶snd (snd (unpremonad M)))))

fmap : ∀ {ℓ} (M :{#} Premonad ℓ) {X Y :{#} Set ℓ} → (X → Y) → (type M X) → (type M Y)
fmap M {X} {Y} f mx = bind M mx ((return M {Y}) ∘ f)

join : ∀ {ℓ} (M :{#} Premonad ℓ) {X :{#} Set ℓ} → type M (type M X) → type M X
join M mmx = bind M mmx id

record IsMonad {ℓ : Level} (M : Premonad ℓ) : Set (lsuc ℓ) where
  constructor monad
  field
    unmonad : ¶Σ[ return-law1 ∈ ({X Y :{#} Set ℓ} {x : X} {k :{¶} X → type M Y} → bind M (return M x) k ≡ k x) ] (
              ¶Σ[ return-law2 ∈ ({X :{#} Set ℓ} {fx : type M X} → bind M fx (return M) ≡ fx) ] (
              ¶Σ[ assoc-law ∈ ({X Y Z :{#} Set ℓ} {fx : type M X} {k : X → type M Y} {q :{¶} Y → type M Z} → bind M (bind M fx k) q ≡ bind M fx (λ x → bind M (k x) q)) ]
              ⊤ ))

open IsMonad public

return-law1 : ∀ {ℓ} {M :{#} Premonad ℓ} (Mmon :{#} IsMonad M) {X Y :{#} Set ℓ} →  {x : X} → {k :{¶} X → type M Y}
                                                  → bind M (return M x) k ≡ k x
return-law1 Mmon = ¶fst(unmonad Mmon)

return-law2 : ∀ {ℓ} {M :{#} Premonad ℓ} (Mmon :{#} IsMonad M) {X :{#} Set ℓ} → {fx : type M X} → bind M fx (return M) ≡ fx
return-law2 Mmon = ¶fst(¶snd(unmonad Mmon))

assoc-law : ∀ {ℓ} {M :{#} Premonad ℓ} (Mmon :{#} IsMonad M) {X Y Z :{#} Set ℓ} {fx : type M X} {k : X → type M Y} {q :{¶} Y → type M Z}
                    → bind M (bind M fx k) q ≡ bind M fx (λ x → bind M (k x) q)
assoc-law Mmon = ¶fst(¶snd(¶snd(unmonad Mmon)))

monad-funct : ∀ {ℓ} (M : Premonad ℓ) → IsMonad M → Functor ℓ ℓ
monad-funct M Mmon = functor [ type M ,
                                 [¶ (λ {X Y :{#} Set _} → fmap M) ,
                                 [¶ (λ {X :{#} Set _} {_} → return-law2 Mmon) ,
                                 tt ] ] ]

record MonadMorphism {ℓ : Level} (M1 M2 : Premonad ℓ) : Set (lsuc ℓ) where
  constructor monad-morphism
  field
    unmonad-morphism : Σ[ morphism ∈ ( {X :{#} Set ℓ} → type M1 X → type M2 X ) ] (
                       ¶Σ[ morph-return-law ∈ ( {X :{#} Set ℓ} {x : X} → morphism (return M1 x) ≡ return M2 x ) ] (
                       ¶Σ[ morph-bind-law ∈ ( {X Y :{#} Set ℓ} {mx : type M1 X} {q : X → type M1 Y}
                                                 → morphism (bind M1 mx q) ≡ bind M2 (morphism mx) (morphism ∘ q) ) ]
                       ⊤ ) )

open MonadMorphism public

morphism : ∀ {ℓ} {M1 M2 : Premonad ℓ} → MonadMorphism M1 M2 → {X :{#} Set ℓ} → type M1 X → type M2 X
morphism {_} {M1} {M2} h = fst(unmonad-morphism h)

morph-return-law : ∀ {ℓ} {M1 M2 :{#} Premonad ℓ} {h :{#} MonadMorphism M1 M2} {X :{#} Set ℓ} {x : X} → morphism h (return M1 x) ≡ return M2 x
morph-return-law {_} {M1} {M2} {h} = ¶fst(snd(unmonad-morphism h))

morph-bind-law : ∀ {ℓ} {M1 M2 :{#} Premonad ℓ} {h :{#} MonadMorphism M1 M2} {X Y :{#} Set ℓ} {mx : type M1 X} {q : X → type M1 Y}
                     → morphism h (bind M1 mx q) ≡ bind M2 (morphism h mx) ((morphism h) ∘ q)
morph-bind-law {_} {M1} {M2} {h} = ¶fst(¶snd(snd(unmonad-morphism h)))
