{-# OPTIONS --cubical --rewriting #-}
module Monads.Return-Join-Isomorphism where

open import TypeSystem
open import Functors
open import Monads.Monads
open import Monads.Return-Join
{-
iso1 : ∀ {ℓ} → Monad-rj ℓ → Monad ℓ
iso1 {ℓ} MA = monad [ premonad  [ (obj (funct MA)) , 
                                [¶ (λ {X :{#} Set _} → η MA) ,
                                [¶ (λ fx k → (μ MA) (hom (funct MA) k fx)) , tt ] ] ] ,
                    [¶ {!(cong (λ x → μ MA x) (η-nat MA) • η-law1 MA)!} ,
                {!(η-law2 MA)
                (cong (λ x → μ MA x) (μ-nat MA) • (μ-law MA) • (cong (λ x → μ MA x) (funct-comp (funct MA) • funct-comp (funct MA))))!} ] ]

iso2 : Monad → Monad-rj ℓ
iso2 M = monad-rj (functor (protofunct M)
                            (λ f Fx → bind M Fx ((return M) ∘ f))
                            (return-law2 M)
                            (assoc-law M • (cong (bind M _) (funext (λ a → return-law1 M)) • cong (bind M _) (funext (λ a → refl _)))))
                   (return M)
                   (λ FFx → bind M FFx id)
                   (return-law1 M)
                   (assoc-law M • (cong (bind M _) (funext λ x → sym (return-law1 M)) • sym (assoc-law M)))
                   (assoc-law M • (cong (bind M _) (funext λ x → sym (return-law1 M)) • sym (assoc-law M)))
                   (return-law1 M)
                   (assoc-law M • (cong (bind M _) (funext λ x → return-law1 M) • return-law2 M))

eq1 : (M : Monad) → iso1 (iso2 M) ≡ M
eq1 (monad protofunctM returnM bindM return-law1M return-law2M assoc-lawM) = {!!}
-}
