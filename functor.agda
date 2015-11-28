module functor where

open import Agda.Primitive

import category

record t ..{ℓ₀⁰ ℓ₀¹ ℓ₁⁰ ℓ₁¹} (𝒞 : category.t ℓ₀⁰ ℓ₁⁰) (𝒟 : category.t ℓ₀¹ ℓ₁¹) : Set (ℓ₀⁰ ⊔ ℓ₀¹ ⊔ ℓ₁¹ ⊔ ℓ₁⁰) where
  module 𝒞 = category.t 𝒞
  module 𝒟 = category.t 𝒟
  field
    act : 𝒞.obj → 𝒟.obj
    map : {a b : _} → 𝒞.hom a b → 𝒟.hom (act a) (act b)

open t public
