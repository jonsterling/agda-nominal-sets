module coproduct where

open import Agda.Primitive

record t ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : A → Set ℓ₁) : Set (ℓ₁ ⊔ ℓ₀) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁

open t public
