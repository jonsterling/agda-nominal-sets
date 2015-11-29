module category where

open import Agda.Primitive

import setoid as S
import coprod as ∐
open ∐ using (_,_)

record t ..ℓ₀ ..ℓ₁ : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  field
    obj : Set ℓ₀
    hom : obj → obj → S.t ℓ₁ lzero
    idn : {a : _} → S.obj (hom a a)
    cmp : {a b c : _} → S.obj ((hom b c S.⊗ hom a b) S.⇒ hom a c)

  field
    .idn-lhs
      : {a b : _}
      → (f : S.obj (hom a b))
      → S.hom (hom a b) (S.act cmp (idn , f)) f
    .idn-rhs
      : {a b : _}
      → (f : S.obj (hom a b))
      → S.hom (hom a b) (S.act cmp (f , idn)) f
    .cmp-ass
      : {a b c d : _}
      → (f : S.obj (hom a b))
      → (g : S.obj (hom b c))
      → (h : S.obj (hom c d))
      → S.hom
          (hom a d)
          (S.act cmp (h , (S.act cmp (g , f))))
          (S.act cmp ((S.act cmp (h , g)) , f))

open t public

op : {ℓ₀ ℓ₁ : _} → t ℓ₀ ℓ₁ → t ℓ₀ ℓ₁
obj (op 𝒞) = t.obj 𝒞
hom (op 𝒞) a b = t.hom 𝒞 b a
idn (op 𝒞) = t.idn 𝒞
S.act (cmp (op 𝒞)) (f , g) = S.act (cmp 𝒞) (g , f)
S.ext (cmp (op 𝒞)) (f , g) = S.ext (cmp 𝒞) (g , f)
idn-lhs (op 𝒞) = idn-rhs 𝒞
idn-rhs (op 𝒞) = idn-lhs 𝒞
cmp-ass (op 𝒞) f g h = S.inv (hom 𝒞 _ _) (cmp-ass 𝒞 h g f)
