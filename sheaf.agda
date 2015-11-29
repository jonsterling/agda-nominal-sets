module sheaf where

open import Agda.Primitive

open import Common
module C where
  module I where
    module SETOID where
      open import Category.Instances.SETOID public
  open import Category public
    hiding (module Map)
  module Map where
    open Category.Map public
    open import Groupoid.Presheaf {Dir.≤} public

import Setoid as S
import Type as T; open T using (_,_)
import coproduct as ∐

-- atomic sheaves
is-atomic-sheaf
  : ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ʰ : _}
  → {𝒞 : C.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → 𝒞 C.Map.⇏₀ᵗ C.I.SETOID.c ℓ₁ᵒ ℓ₁ʰ
  → Set _
is-atomic-sheaf {𝒞 = 𝒞} 𝔉 =
  {e c d : C.obj 𝒞}
    → (f : S.obj (C.homˢ 𝒞 (d , c)))
    → (y : S.obj (𝔉 C.Map.$₀ d))
    → ((g h : S.obj (C.homˢ 𝒞 (e , d)))
         → S.homᵗ
             (C.homˢ 𝒞 (e , c))
             ( C.cmpˢ 𝒞 S.Map.$₀ (f , g)
             , C.cmpˢ 𝒞 S.Map.$₀ (f , h)
             )
         → S.homᵗ
             (𝔉 C.Map.$₀ e)
             ( (C.Map.-$₁ˢ- 𝔉 S.Map.$₀ g) S.Map.$₀ y
             , (C.Map.-$₁ˢ- 𝔉 S.Map.$₀ h) S.Map.$₀ y
             )
      )
    → (let φ x = S.homᵗ (𝔉 C.Map.$₀ d) (y , (C.Map.-$₁ˢ- 𝔉 S.Map.$₀ f) S.Map.$₀ x))
    → ∐.t
        (S.obj (𝔉 C.Map.$₀ c))
        (λ x →
          φ x T.Ten.⊗ (∀ z → φ z → S.homᵗ (𝔉 C.Map.$₀ c) (x , z))
        )

record t
  ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ʰ}
  (𝒞 : C.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    : Set (lsuc ℓ₁ʰ ⊔ lsuc ℓ₁ᵒ ⊔ ℓ₀ˢʰ ⊔ ℓ₀ˢᵒ ⊔ ℓ₀ᵒ) where
  no-eta-equality
  field
    π : 𝒞 C.Map.⇏₀ᵗ C.I.SETOID.c ℓ₁ᵒ ℓ₁ʰ
    .glue : is-atomic-sheaf π
