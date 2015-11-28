module presheaf where

open import Agda.Primitive

import functor
import sets
import category as cat

t : ..{ℓ₀ ℓ₁ : _} ..(ℓ₂ : _) → cat.t ℓ₀ ℓ₁ → Set (lsuc ℓ₂ ⊔ ℓ₁ ⊔ ℓ₀)
t ℓ 𝒞 = functor.t (cat.op 𝒞) (sets.cat ℓ)

cat : ..{ℓ₀ ℓ₁ : _} ..(ℓ₂ : _) → cat.t ℓ₀ ℓ₁ → cat.t (lsuc ℓ₂ ⊔ ℓ₁ ⊔ ℓ₀) (ℓ₂ ⊔ ℓ₀)
cat.obj (cat ℓ 𝒞) = t ℓ 𝒞
cat.hom (cat ℓ 𝒞) F G = (x : _) → functor.act F x → functor.act G x
cat.idn (cat ℓ 𝒞) a x = x
cat.cmp (cat ℓ 𝒞) f g x Fx = f x (g x Fx)
