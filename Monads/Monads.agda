{-# OPTIONS --cubical --rewriting #-}
module Monads.Monads where

open import TypeSystem

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
{-
premonad-⊤-irrelevant : (M : Premonad) (x : ⊤) → premonad [ type M ,
                                                           [¶ (λ {X :{#} Set} → return M {X}) ,
                                                           [¶ (λ {X Y :{#} Set} → bind M {X} {Y}) ,
                                                           x ] ] ]
                                                          ≡ M
premonad-⊤-irrelevant M x = cong (λ y → premonad [ type M ,
                                                  [¶ (λ {X :{#} Set} → return M {X}) ,
                                                  [¶ (λ {X Y :{#} Set} → bind M {X} {Y}) , y ] ] ])
                                  (unique-⊤ x (¶snd (¶snd (snd (unpremonad M)))))
-}
fmap : ∀ {ℓ} (M :{#} Premonad ℓ) {X Y :{#} Set ℓ} → (X → Y) → (type M X) → (type M Y)
fmap M {X} {Y} f mx = bind M mx ((return M {Y}) ∘ f)

join : ∀ {ℓ} (M :{#} Premonad ℓ) {X :{#} Set ℓ} → type M (type M X) → type M X
join M {X} mmx = bind M mmx id

record Monad (ℓ : Level) : Set (lsuc ℓ) where
  constructor monad
  field
    unmonad : Σ[ M ∈ Premonad ℓ ] (
              ¶Σ[ return-law1 ∈ ({X Y :{#} Set ℓ} {x : X} {k : X → type M Y} → bind M (return M x) k ≡ k x) ] (
              ¶Σ[ return-law2 ∈ ({X :{#} Set ℓ} {fx : type M X} → bind M fx (return M) ≡ fx) ] (
              ¶Σ[ assoc-law ∈ ({X Y Z :{#} Set ℓ} {fx : type M X} {k : X → type M Y} {q : Y → type M Z} → bind M (bind M fx k) q ≡ bind M fx (λ x → bind M (k x) q)) ]
              ⊤ )))

open Monad public

m-type : ∀ {ℓ} → Monad ℓ → Set ℓ → Set ℓ
m-type M = type (fst(unmonad M))
 
m-return : ∀ {ℓ} (M :{#} Monad ℓ) → {X :{#} Set ℓ} → X → m-type M X
m-return M = return (fst(unmonad M))

m-bind : ∀ {ℓ} (M :{#} Monad ℓ) → {X Y :{#} Set ℓ} → m-type M X → (X → m-type M Y) → m-type M Y
m-bind M = bind (fst(unmonad M))

return-law1 : ∀ {ℓ} (M :{#} Monad ℓ) {X Y :{#} Set ℓ} {x : X} {k : X → m-type M Y} → m-bind M (m-return M x) k ≡ k x
return-law1 M = ¶fst(snd(unmonad M))

return-law2 : ∀ {ℓ} (M :{#} Monad ℓ) → {X :{#} Set ℓ} {fx : m-type M X} → m-bind M fx (m-return M) ≡ fx
return-law2 M = ¶fst(¶snd(snd(unmonad M)))

assoc-law : ∀ {ℓ} (M :{#} Monad ℓ) → {X Y Z :{#} Set ℓ} {fx : m-type M X} {k : X → m-type M Y} {q : Y → m-type M Z}
                    → m-bind M (m-bind M fx k) q ≡ m-bind M fx (λ x → m-bind M (k x) q)
assoc-law M = ¶fst(¶snd(¶snd(snd(unmonad M))))

m-fmap : ∀ {ℓ} (M :{#} Monad ℓ) {X Y :{#} Set ℓ} → (X → Y) → (m-type M X) → (m-type M Y)
m-fmap M {X} {Y} f mx = m-bind M mx ((m-return M {Y}) ∘ f)

m-fmap-id : ∀ {ℓ} (M :{#} Monad ℓ) {X :{#} Set ℓ} {mx : m-type M X} → m-fmap M id mx ≡ mx
m-fmap-id M {X} {mx} = return-law2 M

monad-to-pre : ∀ {ℓ} → Monad ℓ → Premonad ℓ
monad-to-pre {ℓ} M = premonad [ m-type M ,
                              [¶ (λ {X :{#} Set ℓ} → m-return M {X}) ,
                              [¶ (λ {X Y :{#} Set ℓ} → m-bind M {X} {Y}) ,
                              tt ] ] ]

record MonadMorphism {ℓ : Level} (M1 M2 : Premonad ℓ) : Set (lsuc ℓ) where
  constructor monad-morphism
  field
    unmonad-morphism : Σ[ morphism ∈ ( {X :{#} Set ℓ} → type M1 X → type M2 X ) ] (
                       ¶Σ[ morph-return-law ∈ ( {X :{#} Set ℓ} {x : X} → morphism (return M1 x) ≡ return M2 x ) ] (
                       ¶Σ[ morph-bind-law ∈ ( {X Y :{#} Set ℓ} {mx : type M1 X} {q : X → type M1 Y} → morphism (bind M1 mx q) ≡ bind M2 (morphism mx) (morphism ∘ q) ) ]
                       ⊤ ) )

open MonadMorphism public

morphism : ∀ {ℓ} {M1 M2 : Premonad ℓ} → MonadMorphism M1 M2 → {X :{#} Set ℓ} → type M1 X → type M2 X
morphism {_} {M1} {M2} h = fst(unmonad-morphism h)

morph-return-law : ∀ {ℓ} {M1 M2 :{#} Premonad ℓ} {h :{#} MonadMorphism M1 M2} {X :{#} Set ℓ} {x : X} → morphism h (return M1 x) ≡ return M2 x
morph-return-law {_} {M1} {M2} {h} = ¶fst(snd(unmonad-morphism h))

morph-bind-law : ∀ {ℓ} {M1 M2 :{#} Premonad ℓ} {h :{#} MonadMorphism M1 M2} {X Y :{#} Set ℓ} {mx : type M1 X} {q : X → type M1 Y}
                     → morphism h (bind M1 mx q) ≡ bind M2 (morphism h mx) ((morphism h) ∘ q)
morph-bind-law {_} {M1} {M2} {h} = ¶fst(¶snd(snd(unmonad-morphism h)))
