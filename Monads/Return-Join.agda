{-# OPTIONS --cubical --rewriting #-}
module Monads.Return-Join where

open import TypeSystem
open import Functors
open import Monads.Monads

record Monad-rj (ℓ : Level) : Set (lsuc ℓ) where
  constructor monad-rj
  field
    unmonad-rj : Σ[ F ∈ Functor ℓ ℓ ] (
                 ¶Σ[ η ∈ ({X :{#} Set ℓ} → X → obj F X) ] (
                 ¶Σ[ μ ∈ ({X :{#} Set ℓ} → obj F (obj F X) → obj F X) ] (
                 ¶Σ[ μ-law ∈ ({X :{#} Set ℓ} {f3x : obj F (obj F (obj F X))} → μ (μ f3x) ≡ μ (hom F μ f3x)) ] (
                 ¶Σ[ η-law1 ∈ ({X :{#} Set ℓ} {fx : obj F X} → μ (η fx) ≡ fx) ] (
                 ¶Σ[ η-law2 ∈ ({X :{#} Set ℓ} {fx : obj F X} → μ (hom F η fx) ≡ fx) ] (
                 ⊤ ))))))

open Monad-rj

funct : ∀ {ℓ} → Monad-rj ℓ → Functor ℓ ℓ
funct M = fst (unmonad-rj M)

η : ∀ {ℓ} (M :{#} Monad-rj ℓ) → {X :{#} Set ℓ} → X → obj (funct M) X
η M = ¶fst(snd(unmonad-rj M))

μ : ∀ {ℓ} (M :{#} Monad-rj ℓ) → {X :{#} Set ℓ} → obj (funct M) (obj (funct M) X) → obj (funct M) X
μ M = ¶fst(¶snd(snd(unmonad-rj M)))

η-nat : ∀ {ℓ} (M :{#} Monad-rj ℓ) → {X Y :{#} Set ℓ} {f :{¶} X → Y} {x : X} → hom (funct M) f (η M x) ≡ η M (f x)
η-nat M = NaturalTransformation.naturality (Examples.id-functor) (funct M) (λ (X :{#} Set _) → η M) _ _ _ _

μ-nat : ∀ {ℓ} (M :{#} Monad-rj ℓ) → {X Y :{#} Set ℓ} {f :{¶} X → Y} {f2x : obj (funct M) (obj (funct M) X)}
                 → hom (funct M) f (μ M f2x) ≡ μ M (hom (funct M) (hom (funct M) f) f2x)
μ-nat M = NaturalTransformation.naturality (funct M ∘funct funct M) (funct M) (λ (X :{#} Set _) → μ M) _ _ _ _

μ-law : ∀ {ℓ} (M :{#} Monad-rj ℓ) → {X :{#} Set ℓ} {f3x : obj (funct M) (obj (funct M) (obj (funct M) X))} → μ M (μ M f3x) ≡ μ M (hom (funct M) (μ M) f3x)
μ-law M = ¶fst(¶snd(¶snd(snd(unmonad-rj M))))

η-law1 : ∀ {ℓ} (M :{#} Monad-rj ℓ) → {X :{#} Set ℓ} {fx : obj (funct M) X} → μ M (η M fx) ≡ fx
η-law1 M = ¶fst(¶snd(¶snd(¶snd(snd(unmonad-rj M)))))

η-law2 : ∀ {ℓ} (M :{#} Monad-rj ℓ) → {X :{#} Set ℓ} {fx : obj (funct M) X} → μ M (hom (funct M) (η M) fx) ≡ fx
η-law2 M = ¶fst(¶snd(¶snd(¶snd(¶snd(snd(unmonad-rj M))))))
