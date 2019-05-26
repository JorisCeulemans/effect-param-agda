{-# OPTIONS --cubical --rewriting #-}
module Monads.Return-Join where

open import TypeSystem
open import Functors

record Premonad-rj (ℓ : Level) : Set (lsuc ℓ) where
  constructor premonad-rj
  field
    unpremonad-rj : Σ[ F ∈ Functor ℓ ℓ ] (
                    ¶Σ[ η ∈ ({X :{#} Set ℓ} → X → obj F X) ] (
                    ¶Σ[ μ ∈ ({X :{#} Set ℓ} → obj F (obj F X) → obj F X) ] (
                    ⊤ )))

open Premonad-rj

funct : ∀ {ℓ} → Premonad-rj ℓ → Functor ℓ ℓ
funct M = fst (unpremonad-rj M)

η : ∀ {ℓ} (M :{#} Premonad-rj ℓ) → {X :{#} Set ℓ} → X → obj (funct M) X
η M = ¶fst(snd(unpremonad-rj M))

μ : ∀ {ℓ} (M :{#} Premonad-rj ℓ) → {X :{#} Set ℓ} → obj (funct M) (obj (funct M) X) → obj (funct M) X
μ M = ¶fst(¶snd(snd(unpremonad-rj M)))

η-nat : ∀ {ℓ} (M :{#} Premonad-rj ℓ) → {X Y :{#} Set ℓ} {f :{¶} X → Y} {x : X} → hom (funct M) f (η M x) ≡ η M (f x)
η-nat M = NaturalTransformation.naturality (Examples.id-functor) (funct M) (λ (X :{#} Set _) → η M) _ _ _ _

μ-nat : ∀ {ℓ} (M :{#} Premonad-rj ℓ) → {X Y :{#} Set ℓ} {f :{¶} X → Y} {f2x : obj (funct M) (obj (funct M) X)}
              → hom (funct M) f (μ M f2x) ≡ μ M (hom (funct M) (hom (funct M) f) f2x)
μ-nat M = NaturalTransformation.naturality (funct M ∘funct funct M) (funct M) (λ (X :{#} Set _) → μ M) _ _ _ _

record IsMonad-rj {ℓ : Level} (M : Premonad-rj ℓ) : Set (lsuc ℓ) where
  constructor monad-rj
  field
    unmonad-rj : ¶Σ[ μ-law ∈ ({X :{#} Set ℓ} {f3x : obj (funct M) (obj (funct M) (obj (funct M) X))}
                              → μ M (μ M f3x) ≡ μ M (hom (funct M) (μ M) f3x)) ] (
                 ¶Σ[ η-law1 ∈ ({X :{#} Set ℓ} {fx : obj (funct M) X} → μ M (η M fx) ≡ fx) ] (
                 ¶Σ[ η-law2 ∈ ({X :{#} Set ℓ} {fx : obj (funct M) X} → μ M (hom (funct M) (η M) fx) ≡ fx) ] (
                 ⊤ )))

open IsMonad-rj

μ-law : ∀ {ℓ} {M :{#} Premonad-rj ℓ} (Mmon :{#} IsMonad-rj M) → {X :{#} Set ℓ} {f3x : obj (funct M) (obj (funct M) (obj (funct M) X))}
              → μ M (μ M f3x) ≡ μ M (hom (funct M) (μ M) f3x)
μ-law Mmon = ¶fst(unmonad-rj Mmon)

η-law1 : ∀ {ℓ} {M :{#} Premonad-rj ℓ} (Mmon :{#} IsMonad-rj M) → {X :{#} Set ℓ} {fx : obj (funct M) X} → μ M (η M fx) ≡ fx
η-law1 Mmon = ¶fst(¶snd(unmonad-rj Mmon))

η-law2 : ∀ {ℓ} {M :{#} Premonad-rj ℓ} (Mmon :{#} IsMonad-rj M) → {X :{#} Set ℓ} {fx : obj (funct M) X} → μ M (hom (funct M) (η M) fx) ≡ fx
η-law2 Mmon = ¶fst(¶snd(¶snd(unmonad-rj Mmon)))
