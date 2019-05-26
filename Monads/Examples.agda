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
id-monad {ℓ} = monad [¶ (λ {_ _ :{#} Set ℓ} {_} {_ :{¶} _} → refl _) ,
                     [¶ (λ {_ :{#} Set ℓ} {_} → refl _) ,
                     [¶ (λ {_ _ _ :{#} Set ℓ} {_} {_} {_ :{¶} _} → refl _) ,
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
maybe-assoc-law {ℓ} {X} {Y} {Z} {mx} {k} {q} = maybe {B = λ mx'' → maybe q nothing (maybe k nothing mx'') ≡
                                                                    maybe (λ x → maybe q nothing (k x)) nothing mx''}
                                                     (λ x → refl (maybe q nothing (k x)))
                                                     (refl nothing)
                                                     mx

maybe-monad : ∀ {ℓ} → IsMonad maybe-premonad
maybe-monad {ℓ} = monad [¶ (λ {X Y :{#} Set ℓ} {_} {_ :{¶} _} → refl _ ) ,
                        [¶ (λ {X :{#} Set ℓ} {mx} → maybe-return-law2) ,
                        [¶ (λ {X Y Z :{#} Set ℓ} {mx} {k} {q :{¶} _} → maybe-assoc-law {mx = mx}) ,
                        tt ] ] ]

state-premonad : ∀ {k} ℓ → (S : Set k) → Premonad (k ⊔ ℓ)
state-premonad ℓ S = premonad [ (λ X → (S → X × S)) ,
                              [¶ (λ {X :{#} Set _} x s → [ x , s ]) ,
                              [¶ (λ {X Y :{#} Set _} sx k s → k (fst (sx s)) (snd (sx s))) ,
                              tt ] ] ]

state-monad : ∀ {k ℓ} (S : Set k) → IsMonad (state-premonad ℓ S)
state-monad S = monad [¶ (λ {X Y :{#} Set _} {x} {k :{¶} _} → refl (k x)) ,
                      [¶ (λ {X :{#} Set _} {sx} → refl sx) ,
                      [¶ (λ {X Y Z :{#} Set _} {sx} {k} {q :{¶} _} → refl _) ,
                      tt ] ] ]

record Magma (ℓ : Level) : Set (lsuc ℓ) where
  constructor magma
  field
    unmagma : Σ[ X ∈ (Set ℓ) ]
              ¶Σ[ op ∈ (X → X → X) ]
              ⊤

open Magma

carrier : ∀ {ℓ} → Magma ℓ → Set ℓ
carrier mgm = fst (unmagma mgm)

op : ∀ {ℓ} (mgm :{#} Magma ℓ) → carrier mgm → carrier mgm → carrier mgm
op mgm x y = ¶fst (snd (unmagma mgm)) x y

magma-syntax : ∀ {ℓ} (mgm :{#} Magma ℓ) → carrier mgm → carrier mgm → carrier mgm
magma-syntax = op

syntax magma-syntax mgm x y = x ·⟨ mgm ⟩ y

record IsMonoid {ℓ : Level} (mgm : Magma ℓ) : Set (lsuc ℓ) where
  constructor monoid
  field
    unmonoid : ¶Σ[ e ∈ carrier mgm ]
               ¶Σ[ left-unit ∈ ({x : carrier mgm} → e ·⟨ mgm ⟩ x ≡ x) ]
               ¶Σ[ right-unit ∈ ({x : carrier mgm} → x ·⟨ mgm ⟩ e ≡ x) ]
               ¶Σ[ assoc ∈ ({x y z : carrier mgm} → (x ·⟨ mgm ⟩ y) ·⟨ mgm ⟩ z ≡ x ·⟨ mgm ⟩ (y ·⟨ mgm ⟩ z)) ]
               ⊤

open IsMonoid

mono-unit : ∀ {ℓ} {mgm :{#} Magma ℓ} (mgm-mono :{#} IsMonoid mgm) → carrier mgm
mono-unit mgm-mono = ¶fst (unmonoid mgm-mono)

mono-left-unit : ∀ {ℓ} {mgm :{#} Magma ℓ} (mgm-mono :{#} IsMonoid mgm) {x : carrier mgm} → (mono-unit mgm-mono) ·⟨ mgm ⟩ x ≡ x
mono-left-unit mgm-mono = ¶fst (¶snd (unmonoid mgm-mono))

mono-right-unit : ∀ {ℓ} {mgm :{#} Magma ℓ} (mgm-mono :{#} IsMonoid mgm) {x : carrier mgm} → x ·⟨ mgm ⟩ (mono-unit mgm-mono) ≡ x
mono-right-unit mgm-mono = ¶fst (¶snd (¶snd (unmonoid mgm-mono)))

mono-assoc : ∀ {ℓ} {mgm :{#} Magma ℓ} (mgm-mono :{#} IsMonoid mgm) {x y z : carrier mgm}
                    → (x ·⟨ mgm ⟩ y) ·⟨ mgm ⟩ z ≡ x ·⟨ mgm ⟩ (y ·⟨ mgm ⟩ z)
mono-assoc mgm-mono = ¶fst (¶snd (¶snd (¶snd (unmonoid mgm-mono))))

writer-premonad : ∀ {k} ℓ → (mgm : Magma k) → (m :{¶} carrier mgm) → Premonad (k ⊔ ℓ)
writer-premonad ℓ mgm m = premonad [ (λ X → X × (carrier mgm)) ,
                                   [¶ (λ {X :{#} Set _} x → [ x , m ]) ,
                                   [¶ (λ {X Y :{#} Set _} x,n k → [ fst (k (fst x,n)) , snd x,n ·⟨ mgm ⟩ snd (k (fst x,n)) ]) ,
                                   tt ] ] ]

writer-monad : ∀ {k ℓ} {mgm : Magma k} (mgm-mono : IsMonoid mgm) → IsMonad (writer-premonad ℓ mgm (mono-unit mgm-mono))
writer-monad mgm-mono = monad [¶ (λ {_ _ :{#} Set _} {x} {k} → cong (λ z → [ fst (k x) , z ]) (mono-left-unit mgm-mono)) ,
                              [¶ (λ {_ :{#} Set _} {x,m} → cong (λ z → [ fst x,m , z ]) (mono-right-unit mgm-mono)) ,
                              [¶ (λ {_ _ _ :{#} Set _} {x,m} {k} {q :{¶} _} → cong (λ z → [ (fst (q (fst (k (fst x,m))))) , z ])
                                                                                    (mono-assoc mgm-mono)) ,
                              tt ] ] ]
