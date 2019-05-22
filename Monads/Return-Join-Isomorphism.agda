{-# OPTIONS --cubical --rewriting #-}
module Monads.Return-Join-Isomorphism where

open import TypeSystem
open import Functors
open import Monads.Monads
open import Monads.Return-Join

pmrj-to-pm : ∀ {ℓ} → Premonad-rj ℓ → Premonad ℓ
pmrj-to-pm Mrj = premonad [ obj (funct Mrj) ,
                          [¶ (λ {_ :{#} Set _} → η Mrj) ,
                          [¶ ((λ mx k → (μ Mrj) (hom (funct Mrj) k mx))) ,
                          tt ] ] ]

mrj-to-m : ∀ {ℓ} → (Mrj : Premonad-rj ℓ) → (Mrjmon :{¶} IsMonad-rj Mrj) → IsMonad (pmrj-to-pm Mrj)
mrj-to-m Mrj Mrjmon = monad [¶ (λ {_ _ :{#} Set _} {_} {k} → (cong (λ x → μ Mrj x) {!η-nat Mrj!} • η-law1 Mrjmon)) ,
                            [¶ {!!} ,
                            [¶ {!!} ,
                            tt ] ] ]

m-to-pmrj : ∀ {ℓ} → {M : Premonad ℓ} → (Mmon : IsMonad M) → Premonad-rj ℓ
m-to-pmrj {_} {M} Mmon = premonad-rj [ functor [ type M ,
                                               [¶ ((λ f mx → bind M mx ((return M) ∘ f))) ,
                                               [¶ (λ {_ :{#} Set _} {_} → return-law2 Mmon) ,
                                               tt ] ] ] ,
                                     [¶ (λ {_ :{#} Set _} → return M) ,
                                     [¶ ((λ {_ :{#} Set _} → λ mmx → bind M mmx id)) ,
                                     tt ] ] ]

m-to-mrj : ∀ {ℓ} → {M : Premonad ℓ} → (Mmon : IsMonad M) → IsMonad-rj (m-to-pmrj Mmon)
m-to-mrj {_} {M} Mmon = monad-rj [¶ (λ {_ :{#} Set _} {_} → assoc-law Mmon • (cong (bind M _) (funext λ x → sym (return-law1 Mmon))) • sym (assoc-law Mmon)) ,
                                 [¶ (λ {_ :{#} Set _} {_} → return-law1 Mmon) ,
                                 [¶ (λ {_ :{#} Set _} {_} → assoc-law Mmon • (cong (bind M _) (funext λ x → return-law1 Mmon) • return-law2 Mmon) ) ,
                                 tt ] ] ]

{-
iso1 : ∀ {ℓ} → Monad-rj ℓ → Monad ℓ
iso1 {ℓ} MA = monad [ premonad  [ (obj (funct MA)) , 
                                [¶ (λ {X :{#} Set _} → η MA) ,
                                [¶ (λ fx k → (μ MA) (hom (funct MA) k fx)) , tt ] ] ] ,
                    [¶ {!(cong (λ x → μ MA x) (η-nat MA) • η-law1 MA)!} ,
                {!(η-law2 MA)
                (cong (λ x → μ MA x) (μ-nat MA) • (μ-law MA) • (cong (λ x → μ MA x) (funct-comp (funct MA) • funct-comp (funct MA))))!} ] ]
-}
