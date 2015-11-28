module vec where

open import nat renaming (t to ℕ)
import unit as 𝟙

data t {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  [] : t A 0
  _∷_ : {n : _} → A → t A n → t A (su n)


data _∈_ {ℓ} {A : Set ℓ} (x : A) : {n : ℕ} → t A n → Set ℓ where
  top : {n : ℕ} {xs : t A n} → x ∈ (x ∷ xs)
  pop : {n : ℕ} {xs : t A n} {y : A} → x ∈ xs → x ∈ (y ∷ xs)
