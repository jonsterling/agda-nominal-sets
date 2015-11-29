module fin-mono where

open import Agda.Primitive

import list
import Category as C
import Type as T; open T using (_,_)
import Setoid as S

open S.Map using (_$₀_; _$₁_)

module _ ..{ℓ : _} where
  module _ {𝒮 : Set ℓ} (xs ys : list.t 𝒮) where
    _↪₀_ : Set ℓ
    _↪₀_ = {x : _} → x list.∈ xs → x list.∈ ys

    _↪_ : S.t S.Dir.≈ ℓ lzero
    _↪_ = S.T↑S _↪₀_

  cat
    : Set ℓ
    → C.t ℓ ℓ lzero
  C.obj (cat 𝒮) =
    list.t 𝒮
  C.homˢ (cat 𝒮) (xs , ys) =
    xs ↪ ys
  _$₀_ (C.idnˢ (cat 𝒮)) =
    λ _ i → i
  _$₁_ (C.idnˢ (cat 𝒮)) =
    _
  _$₀_ (C.G.cmpˢ (cat 𝒮)) (f , g) =
    λ x → f (g x)
  _$₁_ (C.cmpˢ (cat 𝒮)) =
    _
  C.idn-lhs (cat 𝒮) =
    _
  C.idn-rhs (cat 𝒮) =
    _
  C.cmp-ass (cat 𝒮) =
    _
  C.invˢ (cat 𝒮) =
    _
  C.inv-lhs (cat 𝒮) =
    _
  C.inv-rhs (cat 𝒮) =
    _
