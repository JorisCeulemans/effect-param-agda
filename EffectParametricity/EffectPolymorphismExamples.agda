{-# OPTIONS --cubical --rewriting #-}
module EffectParametricity.EffectPolymorphismExamples where

open import TypeSystem
open import Monads.Monads
{-
sequence : ∀ {ℓ} (M :{#} Premonad ℓ) {X :{#} Set ℓ} → List (type M X) → type M (List X)
sequence M l = list (return M []) (λ mx lt seq-lt → bind M mx (λ x → bind M seq-lt (λ ltx → return M (x :: ltx)))) l

f1 : (M :{#} Premonad lzero) → List (type M Bool) → type M Bool
f1 M l = list (return M true) (λ mb lt f1lt → bind M mb (λ b → if b then f1lt else return M false)) l

-- The following two functions are also described in Voigtländer (2009).
f2 : (M :{#} Premonad lzero) → List (type M Nat) → type M Nat
f2 M l = bind M (sequence M l) (λ lnat → return M (sum lnat))

f3 : (M :{#} Premonad lzero) → List (type M Nat) → type M Nat
f3 M = (f2 M) ∘ reverse
-}
