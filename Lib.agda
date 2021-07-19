{-# OPTIONS --rewriting #-}

module Lib where

open import Agda.Primitive public

private
  variable
    i j k : Level
    A : Set i
    B : Set j

record 𝟙 : Set where
  constructor *
open 𝟙 public

data 𝟘 : Set where

exfalso : 𝟘 → A
exfalso ()

record Σ̂ (A : Set i)(B : A → Set j) : Set (i ⊔ j) where
  constructor _⸴_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ̂ public

data _⊎_ (A : Set i)(B : Set j) : Set (i ⊔ j) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

ind⊎ : (P : A ⊎ B → Set k)
     → (∀ x → P (inj₁ x))
     → (∀ y → P (inj₂ y))
     → ∀ t
     → P t
ind⊎ P u v (inj₁ x) = u x
ind⊎ P u v (inj₂ y) = v y

case⊎ : {C : Set k} → A ⊎ B → (A → C) → (B → C) → C
case⊎ t u v = ind⊎ _ u v t

record ↑ℓ (A : Set i){j} : Set (i ⊔ j) where
  constructor ↑[_]↑
  field
    ↓[_]↓ : A
open ↑ℓ public

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data _≡_ {A : Set i}(x : A) : A → Set i where
  rfl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

Ĵ : {x : A}(P : ∀ {y} → x ≡ y → Set j)
  → P rfl
  → ∀ {y}(p : x ≡ y)
  → P p
Ĵ P Prfl rfl = Prfl

transport : (P : A → Set j){x y : A}
          → x ≡ y
          → P x
          → P y
transport P p Px = Ĵ _ Px p
