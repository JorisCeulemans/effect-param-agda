{-# OPTIONS --cubical --rewriting #-}
module Monads.Examples where

open import TypeSystem
open import Monads.Monads

id-premonad : ∀ {ℓ} → Premonad ℓ
id-premonad = premonad [ id ,
                       [¶ (λ x → x) ,
                       [¶ (λ x k → k x) ,
                       tt ] ] ]           

id-monad : ∀ {ℓ} → IsMonad id-premonad
id-monad {ℓ} = monad [¶ (λ {_ _ :{#} Set ℓ} {_} {_} → refl _) ,
                     [¶ (λ {_ :{#} Set ℓ} {_} → refl _) ,
                     [¶ (λ {_ _ _ :{#} Set ℓ} {_} {_} {_} → refl _) ,
                     tt ] ] ]

maybe-premonad : ∀ {ℓ} → Premonad ℓ
maybe-premonad {ℓ} = premonad [ Maybe ,
                              [¶ (λ {X :{#} Set ℓ} x → just x) ,
                              [¶ (λ {X Y :{#} Set ℓ} mx k → maybe k nothing mx) ,
                              tt ] ] ]

maybe-return-law2 : ∀ {ℓ} {X :{#} Set ℓ} {mx : Maybe X} → maybe just nothing mx ≡ mx
maybe-return-law2 {ℓ} {_} {mx} = maybe {B = λ mx' → maybe just nothing mx' ≡ mx'} (λ x → refl (just x)) (refl nothing) mx

maybe-assoc-law : ∀ {ℓ} {X Y Z :{#} Set ℓ} {mx : Maybe X} {k : X → Maybe Y} {q : Y → Maybe Z}
                           → maybe {B = λ mx' → Maybe Z} q nothing (maybe k nothing mx) ≡ maybe (λ x → maybe q nothing (k x)) nothing mx
maybe-assoc-law {ℓ} {X} {Y} {Z} {mx} {k} {q} = maybe {B = λ mx'' → maybe q nothing (maybe k nothing mx'') ≡ maybe (λ x → maybe q nothing (k x)) nothing mx''}
                                                     (λ x → refl (maybe q nothing (k x)))
                                                     (refl nothing)
                                                     mx

maybe-monad : ∀ {ℓ} → IsMonad maybe-premonad
maybe-monad {ℓ} = monad [¶ (λ {X Y :{#} Set ℓ} {_} {_} → refl _ ) ,
                        [¶ (λ {X :{#} Set ℓ} {mx} → maybe-return-law2) ,
                        [¶ (λ {X Y Z :{#} Set ℓ} {mx} {k} {q} → maybe-assoc-law {mx = mx}) ,
                        tt ] ] ]

record Magma (ℓ : Level) : Set (lsuc ℓ) where
  constructor magma
  field
    unmagma : Σ[ X ∈ (Set ℓ) ]
              ¶Σ[ op ∈ (X → X → X) ]
              ⊤

open Magma

carrier : ∀ {ℓ} → Magma ℓ → Set ℓ
carrier M = fst (unmagma M)

op : ∀ {ℓ} (M :{#} Magma ℓ) → carrier M → carrier M → carrier M
op M x y = ¶fst (snd (unmagma M)) x y

magma-syntax : ∀ {ℓ} (M :{#} Magma ℓ) → carrier M → carrier M → carrier M
magma-syntax = op

syntax magma-syntax M x y = x ·⟨ M ⟩ y

writer-premonad : ∀ {k ℓ} → (M : Magma k) → (m :{¶} carrier M) → Premonad (k ⊔ ℓ)
writer-premonad M m = premonad [ (λ X → X × (carrier M)) ,
                               [¶ (λ {X :{#} Set _} x → [ x , m ]) ,
                               [¶ (λ {X Y :{#} Set _} x,n k → [ fst (k (fst x,n)) , snd x,n ·⟨ M ⟩ snd (k (fst x,n)) ]) ,
                               tt ] ] ]

