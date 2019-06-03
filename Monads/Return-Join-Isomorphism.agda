{-# OPTIONS --cubical --rewriting #-}
module Monads.Return-Join-Isomorphism where

open import TypeSystem
open import Functors
open import Monads.Monads
open import Monads.Return-Join

pmrj-to-pm : ∀ {ℓ} → Premonad-rj ℓ → Premonad ℓ
pmrj-to-pm Mrj = premonad [ obj (funct Mrj) ,
                          [¶ (λ {_ :{#} Set _} → η Mrj) ,
                          [¶ ((λ mx (k :{¶} _) → (μ Mrj) (hom (funct Mrj) k mx))) ,
                          tt ] ] ]

mrj-to-m : ∀ {ℓ} → (Mrj : Premonad-rj ℓ) → (Mrjmon : IsMonad-rj Mrj) → IsMonad (pmrj-to-pm Mrj)
mrj-to-m Mrj Mrjmon = monad [¶ (λ {_ _ :{#} Set _} {_} {k :{¶} _} → (cong (λ x → μ Mrj x) (η-nat Mrj) • η-law1 Mrjmon)) ,
                            [¶ (λ {_ :{#} Set _} {_} → η-law2 Mrjmon) ,
                            [¶ (λ {_ _ _ :{#} Set _} {_} {k :{¶} _} {q :{¶} _} → cong (λ x → μ Mrj x) ({!μ-nat Mrj!})
                                                                           • μ-law Mrjmon
                                                                           • cong (λ x → μ Mrj x) (funct-comp • funct-comp)) ,
                            tt ] ] ]
                      where
                        funct-comp : {X Y Z :{#} Set _} {f :{¶} X → Y} {g :{¶} Y → Z} {mx : obj (funct Mrj) X}
                                        → hom (funct Mrj) g (hom (funct Mrj) f mx) ≡ hom (funct Mrj) (g ∘ f) mx
                        funct-comp {X} {Y} {Z} {f} {g} {mx} = Composition.composition (funct Mrj) X Y Z f g mx

m-to-pmrj : ∀ {ℓ} → {M : Premonad ℓ} → (Mmon : IsMonad M) → Premonad-rj ℓ
m-to-pmrj {_} {M} Mmon = premonad-rj [ monad-funct Mmon ,
                                     [¶ (λ {_ :{#} Set _} → return M) ,
                                     [¶ ((λ {_ :{#} Set _} mmx → bind M mmx id)) ,
                                     tt ] ] ]

m-to-mrj : ∀ {ℓ} → {M : Premonad ℓ} → (Mmon : IsMonad M) → IsMonad-rj (m-to-pmrj Mmon)
m-to-mrj {_} {M} Mmon = monad-rj [¶ (λ {_ :{#} Set _} {_} → assoc-law Mmon
                                                             • (cong ({!bind M _!}) (funext λ x → sym (return-law1 Mmon)))
                                                             • sym (assoc-law Mmon)) ,
                                 [¶ (λ {_ :{#} Set _} {_} → return-law1 Mmon) ,
                                 [¶ (λ {_ :{#} Set _} {_} → assoc-law Mmon
                                                             • (cong ({!bind M _!}) (funext λ x → return-law1 Mmon)
                                                             • return-law2 Mmon) ) ,
                                 tt ] ] ]
