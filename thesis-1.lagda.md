
```agda
{-# OPTIONS --without-K #-}

module thesis-1 where

open import Agda.Primitive public
  renaming ( Set to type
           ; lzero to ℓ0
           ; Setω to typeω
           )
  using    (Level ; lsuc ; _⊔_)

𝓤 : type (lsuc ℓ0)
𝓤 = type ℓ0

type-of : {ℓ : Level} {A : type ℓ} (a : A) → type ℓ
type-of {ℓ} {A} a = A

residing-universe-level : {ℓ : Level} (A : type ℓ) → Level
residing-universe-level {ℓ = ℓ} A = ℓ
```

