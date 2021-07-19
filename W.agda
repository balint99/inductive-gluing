module W where

open import Lib

private
  variable
    i j k : Level
    S : Set i
    P : S → Set j

data W (S : Set i)(P : S → Set j) : Set (i ⊔ j) where
  sup : ∀ s → (P s → W S P) → W S P

data PW (S : Set i)(P : S → Set j) : W S P → Set (i ⊔ j) where
  Psup : ∀ {s f} → (∀ p → PW S P (f p)) → PW S P (sup s f)

pw : ∀ w → PW S P w
pw (sup s f) = Psup (λ p → pw (f p))
