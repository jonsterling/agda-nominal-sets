module coprod where

open import Agda.Primitive
import identification as ≡

record t ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : A → Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁

open t public

syntax t A (λ x → B) = [ x ∶ A ] B

record !t ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : A → Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  constructor _,_!_
  field
    !π₁ : A
    !π₂ : B !π₁
    !unique : (b : B !π₁) → ≡.t !π₂ b

open !t public

syntax !t A (λ x → B) = ![ x ∶ A ] B

_⊗_ : ..{ℓ₀ ℓ₁ : _} (A : Set ℓ₀) (B : Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
A ⊗ B = [ _ ∶ A ] B
