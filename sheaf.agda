module sheaf where

open import Agda.Primitive

import category as cat
import presheaf as psh
import coprod as ∐
import identification as ≡
import functor

-- atomic sheaves
is-sheaf : ..{ℓ₀ ℓ₁ ℓ₂ : _} {𝒞 : cat.t ℓ₀ ℓ₁} (𝔉 : psh.t ℓ₂ 𝒞) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
is-sheaf {𝒞 = 𝒞} 𝔉 =
  {e c d : 𝒞.obj}
  (f : 𝒞.hom d c)
  (y : 𝔉.act d)
    → ((g h : 𝒞.hom e d) → ≡.t (𝒞.cmp f g) (𝒞.cmp f h) → ≡.t (𝔉.map g y) (𝔉.map h y))
    → ∐.![ x ∶ 𝔉.act c ] ≡.t y (𝔉.map f x)
  where
    module 𝒞 = cat.t 𝒞
    module 𝔉 = functor.t 𝔉

record t ..{ℓ₀ ℓ₁} ..(ℓ₂ : _) (𝒞 : cat.t ℓ₀ ℓ₁) : Set (ℓ₀ ⊔ ℓ₁ ⊔ lsuc ℓ₂) where
  field
    π : psh.t ℓ₂ 𝒞
    law : is-sheaf π

open t public
