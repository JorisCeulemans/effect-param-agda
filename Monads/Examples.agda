{-# OPTIONS --cubical --rewriting #-}
module Monads.Examples where

open import TypeSystem
open import Monads.Monads

id-premonad : ∀ {ℓ} → Premonad ℓ
id-premonad = premonad [ id ,
                       [¶ (λ x → x) ,
                       [¶ (λ x k → k x) ,
                       tt ] ] ]           

id-monad : ∀ {ℓ} → Monad ℓ
id-monad {ℓ} = monad [ premonad [ id , 
                            [¶ (λ x → x) ,
                            [¶ (λ x k → k x) ,
                            tt ] ] ] ,
                     [¶ (λ {_ _ :{#} Set ℓ} {_} {_} → refl _) ,
                     [¶ (λ {_ :{#} Set ℓ} {_} → refl _) ,
                     [¶ (λ {_ _ _ :{#} Set ℓ} {_} {_} {_} → refl _) ,
                     tt ] ] ] ]
