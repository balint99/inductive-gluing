module Reduction where

open import Lib

private
  variable
    a b c d : Level
{-
data W (S : Set a)(P : S → Set b) : Set (a ⊔ b) where
  sup : (s : S) → (P s → W S P) → W S P

module _ (I : Set a)(S : I → Set b)(P : ∀ {i} → S i → I → Set c) where
  S' : Set (a ⊔ b)
  S' = Σ̂ I S

  P' : S' → Set (a ⊔ c)
  P' (i ⸴ s) = Σ̂ I (P s)

  Pre : Set (a ⊔ b ⊔ c)
  Pre = W S' P'

  ix : Pre → I
  ix (sup (i ⸴ s) f) = i

  good : Pre → Set (a ⊔ c)
  good (sup s' f) = ∀ {j} p → (ix (f (j ⸴ p)) ≡ j) ×̂ good (f (j ⸴ p))

  IW' : I → Set (a ⊔ b ⊔ c)
  IW' i = Σ̂ Pre (λ w → (ix w ≡ i) ×̂ good w)

module _ {I : Set a}{S : I → Set b}{P : ∀ {i} → S i → I → Set c} where
  sup' : ∀ {i}(s : S i) → (∀ {j} → P s j → IW' I S P j) → IW' I S P i
  sup' {i} s f = sup (i ⸴ s) (λ jp → proj₁ (f (proj₂ jp))) ⸴ (rfl ⸴ λ p → proj₂ (f p))

  elim' : (Q : ∀ {i} → IW' I S P i → Set d)
        → (∀ {i}(s : S i){f : ∀ {j} → P s j → IW' I S P j}
           → (∀ {j}(p : P s j) → Q (f p)) → Q (sup' s f))
        → ∀ {i}(w : IW' I S P i) → Q w
  elim' Q g (sup (i ⸴ s) f ⸴ (rfl ⸴ h)) = g s (λ {j} p → elim' Q g (f (j ⸴ p) ⸴ h p))

  elimβ' : ∀ {i}{s : S i}{f : ∀ {j} → P s j → IW' I S P j}
           {Q : ∀ {i} → IW' I S P i → Set d}
           {g : ∀ {i}(s : S i){f : ∀ {j} → P s j → IW' I S P j}
              → (∀ {j}(p : P s j) → Q (f p)) → Q (sup' s f)}
         → elim' Q g (sup' s f) ≡ g s (λ p → elim' Q g (f p))
  elimβ' = rfl
-}

data W (S : Set a)(P : S → Set b) : Set (a ⊔ b) where
  sup : (s : S) → (P s → W S P) → W S P

elimW : ∀ {S : Set a}{P : S → Set b}(Q : W S P → Set c)
      → ((s : S)(f : P s → W S P) → ((p : P s) → Q (f p)) → Q (sup s f))
      → (w : W S P) → Q w
elimW Q v (sup s f) = v s f (λ p → elimW Q v (f p))

module _ (I : Set a)(S : I → Set b)(P : (i : I) → S i → I → Set c) where
  S' : Set (a ⊔ b)
  S' = Σ̂ I S

  P' : S' → Set (a ⊔ c)
  P' = λ s' → Σ̂ I (P (proj₁ s') (proj₂ s'))

  Pre : Set (a ⊔ b ⊔ c)
  Pre = W S' P'

  ix : Pre → I
  ix = elimW (λ _ → I) (λ s' _ _ → proj₁ s')

  good : Pre → Set (a ⊔ c)
  good = elimW (λ _ → Set (a ⊔ c))
               (λ s' f' r' → (j : I)(p : P (proj₁ s') (proj₂ s') j)
                           → (ix (f' (j ⸴ p)) ≡ j) ×̂ r' (j ⸴ p))

  W' : I → Set (a ⊔ b ⊔ c)
  W' = λ i → Σ̂ Pre (λ pre → (ix pre ≡ i) ×̂ good pre)

module _ {I : Set a}{S : I → Set b}{P : (i : I) → S i → I → Set c} where
  sup' : (i : I)(s : S i) → ((j : I) → P i s j → W' I S P j) → W' I S P i
  sup' = λ i s f → sup (i ⸴ s) (λ jp → proj₁ (f (proj₁ jp) (proj₂ jp)))
                 ⸴ (rfl ⸴ λ j p → proj₂ (f j p))

  elimW' : (Q : (i : I) → W' I S P i → Set d)
         → ((i : I)(s : S i)(f : (j : I) → P i s j → W' I S P j)
           → ((j : I)(p : P i s j) → Q j (f j p))
           → Q i (sup' i s f))
         → (i : I)(w : W' I S P i) → Q i w
  elimW' = λ Q v i w →
    elimW (λ pre → (i : I)(eg : (ix _ _ _ pre ≡ i) ×̂ good _ _ _ pre) → Q i (pre ⸴ eg))
          (λ s' f' r' → λ i eg →
             Ĵ (λ {i} e → Q i (sup s' f' ⸴ (e ⸴ proj₂ eg)))
               (v (proj₁ s') (proj₂ s') (λ j p → f' (j ⸴ p) ⸴ proj₂ eg j p)
                  (λ j p → r' (j ⸴ p) j (proj₂ eg j p)))
               {i} (proj₁ eg))
          (proj₁ w) i (proj₂ w)

  elimWβ' : ∀ {i s f}{Q : (i : I) → W' I S P i → Set d}
            {v : (i : I)(s : S i)(f : (j : I) → P i s j → W' I S P j)
               → ((j : I)(p : P i s j) → Q j (f j p)) → Q i (sup' i s f)}
          → elimW' Q v i (sup' i s f) ≡ v i s f (λ j p → elimW' Q v j (f j p))
  elimWβ' = rfl
{-
  elimW' Q v i (sup' i s f) = elimW' Q v i (sup (i ⸴ s) (λ jp → proj₁ (f (proj₁ jp) (proj₂ jp))) ⸴ (rfl ⸴ λ j p → proj₂ (f j p)))
    = elimW Q' v' (sup (i ⸴ s) (λ jp → proj₁ (f (proj₁ jp) (proj₂ jp)))) i (rfl ⸴ λ j p → proj₂ (f j p))
    = v' (i ⸴ s) (λ jp → proj₁ (f (proj₁ jp) (proj₂ jp))) (λ jp → elimW Q' v' (proj₁ (f (proj₁ jp) (proj₂ jp)))) i (rfl ⸴ λ j p → proj₂ (f j p))
    = Ĵ Q'' v'' {i} rfl
    = v i s (λ j p → proj₁ (f j p) ⸴ proj₂ (f j p)) (λ j p → elimW Q' v' (proj₁ (f j p)) j (proj₂ (f j p)))
    = v i s f (λ j p → elimW' Q v j (f j p))
-}
