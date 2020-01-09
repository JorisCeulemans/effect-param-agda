{-# OPTIONS --cubical --rewriting #-}
module Monads.Examples where

-- open import PointwiseEquality
open import TypeSystem
open import Monads.Monads
id-premonad : ∀ {ℓ} → Premonad ℓ
id-premonad = premonad [ id ,
                       [¶ (λ x → x) ,
                       [¶ (λ x k → k x) ,
                       tt ] ] ]           

id-monad : ∀ {ℓ} → IsMonad id-premonad
id-monad {ℓ} = monad [¶ (λ {_ _ :{#} Set ℓ} {x :{¶} _} {q :{¶} _} → ¶refl (q x)) ,
                     [¶ (λ {_ :{#} Set ℓ} {x :{¶} _} → ¶refl x) ,
                     [¶ (λ {_ _ _ :{#} Set ℓ} {x :{¶} _} {k :{¶} _} {q :{¶} _} → ¶refl (q (k x))) ,
                     tt ] ] ]

maybe-premonad : ∀ {ℓ} → Premonad ℓ
maybe-premonad {ℓ} = premonad [ Maybe ,
                              [¶ (λ {X :{#} Set ℓ} x → just x) ,
                              [¶ (λ {X Y :{#} Set ℓ} mx k → maybe¶ k nothing mx) ,
                              tt ] ] ]

maybe-return-law2 : ∀ {ℓ} {X :{#} Set ℓ} (mx :{¶} Maybe X) → maybe¶ just nothing mx ¶≡ mx
maybe-return-law2 {ℓ} {_} mx = maybe¶ {B = λ mx' → maybe¶ just nothing mx' ¶≡ mx'} (λ x → ¶refl (just x)) (¶refl nothing) mx

maybe-assoc-law : ∀ {ℓ} {X Y Z :{#} Set ℓ} (mx :{¶} Maybe X) (k :{¶} (x :{¶} X) → Maybe Y) (q :{¶} (y :{¶} Y) → Maybe Z)
                           → maybe¶ {B = λ mx' → Maybe Z} q nothing (maybe¶ k nothing mx) ¶≡ maybe¶ (λ x → maybe¶ q nothing (k x)) nothing mx
maybe-assoc-law {ℓ} {X} {Y} {Z} mx k q = maybe¶ {B = λ mx'' → maybe¶ q nothing (maybe¶ k nothing mx'') ¶≡
                                                               maybe¶ {B = λ x → Maybe Z} (λ x → maybe¶ q nothing (k x)) nothing mx''}
                                                (λ x → ¶refl (maybe¶ q nothing (k x)))
                                                (¶refl nothing)
                                                mx

maybe-monad : ∀ {ℓ} → IsMonad maybe-premonad
maybe-monad {ℓ} = monad [¶ (λ {X Y :{#} Set ℓ} {x :{¶} _} {q :{¶} _} → ¶refl (q x) ) ,
                        [¶ (λ {X :{#} Set ℓ} {mx :{¶} _} → maybe-return-law2 mx) ,
                        [¶ (λ {X Y Z :{#} Set ℓ} {mx :{¶} _} {k :{¶} _} {q :{¶} _} → maybe-assoc-law mx k q) ,
                        tt ] ] ]

state-premonad : ∀ {k} ℓ → (S : Set k) → Premonad (k ⊔ ℓ)
state-premonad ℓ S = premonad [ (λ X → ((_ :{¶} S) → X × S)) ,
                              [¶ (λ {X :{#} Set _} x s → [ x , s ]) ,
                              [¶ (λ {X Y :{#} Set _} sx k s → k (fst (sx s)) (snd (sx s))) ,
                              tt ] ] ]

state-monad : ∀ {k ℓ} (S : Set k) → IsMonad (state-premonad ℓ S)
state-monad S = monad [¶ (λ {X Y :{#} Set _} {x :{¶} _} {k :{¶} _} → ¶refl (k x)) ,
                      [¶ (λ {X :{#} Set _} {sx :{¶} _} → ¶refl sx) ,
                      [¶ (λ {X Y Z :{#} Set _} {sx :{¶} _} {k :{¶} _} {q :{¶} _} → refl _) ,
                      tt ] ] ]
{-
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
                              [¶ (λ {_ _ _ :{#} Set _} {x,m} {k} {q} → cong (λ z → [ (fst (q (fst (k (fst x,m))))) , z ])
                                                                             (mono-assoc mgm-mono)) ,
                              tt ] ] ]

wr-monad-monoid : ∀ {k ℓ} {X : Set (k ⊔ ℓ)} {x :{¶} X} {mgm : Magma k} {m :{¶} carrier mgm}
                                            → IsMonad (writer-premonad ℓ mgm m) → IsMonoid mgm
wr-monad-monoid {_} {_} {X} {x} {mgm} {m} wr-mon = monoid [¶ m ,
                                                          [¶ (λ {n} → cong snd (return-law1 wr-mon {X = X} {x = x} {k = λ z → [ z , n ]})) ,
                                                          [¶ (λ {n} → cong snd (return-law2 wr-mon {X = X} {fx = [ x , n ]})) ,
                                                          [¶ (λ {n1 n2 n3} → cong snd (assoc-law wr-mon {X = X} {Y = X} {Z = X} {fx = [ x , n1 ]}
                                                                                                  {k = λ z → [ z , n2 ]} {q = λ z → [ z , n3 ]})) ,
                                                          tt ] ] ] ]

return-morphism : ∀ {ℓ} (M : Premonad ℓ) (Mmon : IsMonad M) → MonadMorphism (id-premonad {ℓ}) M
return-morphism M Mmon = monad-morphism [ (λ {X :{#} Set _} → return M) ,
                                        [¶ (λ {X :{#} Set _} {x} → refl (return M x)) ,
                                        [¶ (λ {X Y :{#} Set _} {mx} {q} → sym (return-law1 Mmon)) ,
                                        tt ] ] ]
-}
