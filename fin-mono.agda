module fin-mono where

import list
import Category as C
import Type as T; open T using (_,_)
import Setoid as S

open S.Map using (_$₀_; _$₁_)

_↪₀_ : {ℓ : _} {𝒮 : Set ℓ} → list.t 𝒮 → list.t 𝒮 → Set ℓ
xs ↪₀ ys = {x : _} → x list.∈ xs → x list.∈ ys

squash : {d : _} ..{ℓᵒ ℓʰ : _} (A : S.t d ℓᵒ ℓʰ) → S.t d ℓᵒ ℓʰ
S.obj (squash A) = S.obj A
S.homᵗ (squash A) _ = T.𝟙.t
S.idnᵗ (squash A) _ = T.*
S.cmpᵗ (squash A) _ = T.*
S.invᵗ (squash {S.Dir.≤} A) = T.*
S.invᵗ (squash {S.Dir.≈} A) _ = T.*

_↪_ : {ℓᵒ : _} {𝒮 : Set ℓᵒ} → list.t 𝒮 → list.t 𝒮 → S.t S.Dir.≈ ℓᵒ ℓᵒ
xs ↪ ys = squash (S.≡.s (xs ↪₀ ys))

cat : {ℓ : _} (𝒮 : Set ℓ) → C.t ℓ ℓ ℓ
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
