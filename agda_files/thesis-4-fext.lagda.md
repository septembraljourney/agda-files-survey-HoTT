Import
```agda
{-#  OPTIONS --without-K  #-}

module thesis-4-fext where

open import thesis-3-equiv public
```


function extensionality
```agda
happ : {X : type ℓ} {𝓟 : X → type ℓ'} {f g : Π 𝓟}
      → f ＝ g → f ∼ g
happ p x = ap (λ - → - x) p
fextⁱ = happ

postulate
  FEXT : {X : type ℓ} {𝓟 : X → type ℓ'} {f g : Π 𝓟}
       → equiv (happ {f = f} {g = g})
```


Gadgets of function extensionality
```agda
FEXT-ivtbl : {X : type ℓ} {𝓟 : X → type ℓ'} {f g : Π 𝓟}
           → ivtbl (happ {f = f} {g = g})
FEXT-ivtbl = equiv-ivtbl (FEXT)

fext : {X : type ℓ} {𝓟 : X → type ℓ'} {f g : Π 𝓟}
     →  f ∼ g → f ＝ g
fext = ivtbl.inv (FEXT-ivtbl)

fext-s : {X : type ℓ} {𝓟 : X → type ℓ'} {f g : Π 𝓟}
       → (happ {f = f} {g = g}) ∘ (fext {f = f} {g = g}) ∼ id
fext-s = ivtbl.inv-s (FEXT-ivtbl)

fext-r : {X : type ℓ} {𝓟 : X → type ℓ'} {f g : Π 𝓟}
       → (fext {f = f} {g = g}) ∘ (happ {f = f} {g = g}) ∼ id
fext-r {f} {g} = ivtbl.inv-r (FEXT-ivtbl)
```
