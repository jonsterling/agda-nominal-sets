module category where

open import Agda.Primitive

record t ..ℓ₀ ..ℓ₁ : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  field
    obj : Set ℓ₀
    hom : obj → obj → Set ℓ₁
    idn : {a : _} → hom a a
    cmp : {a b c : _} → hom b c → hom a b → hom a c

open t public

module _ {ℓ₀ ℓ₁} where
  op : t ℓ₀ ℓ₁ → t ℓ₀ ℓ₁
  obj (op 𝒞) = t.obj 𝒞
  hom (op 𝒞) a b = t.hom 𝒞 b a
  idn (op 𝒞) = t.idn 𝒞
  cmp (op 𝒞) f g = t.cmp 𝒞 g f
