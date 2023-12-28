Import
```agda
{-#  OPTIONS --without-K  #-}

module thesis-3-htpy where

open import thesis-2 public
```


Definition of homotopy
```agda
_∼_ : {X : type ℓ} {𝓟 : X → type ℓ'}
    → Π 𝓟 → Π 𝓟 → type (ℓ ⊔ ℓ')
_∼_ {X = X} f g = (x : X) → f x ＝ g x
infix 0 _∼_
```

Basic property - refl, inverse, concat
```agda
ht-refl : {A : type ℓ} {𝓟 : A → type ℓ'}
        → (f : Π 𝓟) → f ∼ f
ht-refl f = λ - → refl _

_ʰⁱ :{A : type ℓ} {𝓟 : A → type ℓ'} {f g : Π 𝓟}
    → f ∼ g → g ∼ f
H ʰⁱ = λ x → sym (H x)
ht-sym = _ʰⁱ

_∙ₕ_ : {A : type ℓ} {𝓟 : A → type ℓ'} {f g h : Π 𝓟}
     → f ∼ g → g ∼ h → f ∼ h
H ∙ₕ K = λ x → H x ∙ K x
ht∙ = _∙ₕ_
infixl 20 _∙ₕ_
```


Homotopies are natural transformations
```agda
ht-nat : {A : type ℓ} {B : type ℓ'} {f g : A → B} {x y : A}
       → (H : f ∼ g) (p : x ＝ y) → (H x) ∙ (ap g p) ＝ (ap f p) ∙ (H y)
ht-nat {x = x} H (refl x) = ∙-refl-r (H x)

ht-nat-u : {A : type ℓ} {B : type ℓ'} {f g : A → B} {x y : A}
       → (H : f ∼ g) (p : x ＝ y) → (H x) ∙ (ap g p) ∙ (H y) ⁻¹ ＝ ap f p
ht-nat-u {f = f} {g = g} {x = x} H (refl x)
  = H x ∙ refl (g x) ∙ H x ⁻¹ ＝⟨ ap (λ - → - ∙ H x ⁻¹) (∙-refl-r (H x)) ⟩
    H x ∙ H x ⁻¹ ＝⟨ ∙-sym-r (H x) ⟩
    refl _ ∎

ht-nat-d : {A : type ℓ} {B : type ℓ'} {f g : A → B} {x y : A}
       → (H : f ∼ g) (p : x ＝ y) → (H x) ⁻¹ ∙ (ap f p) ∙ (H y) ＝ ap g p
ht-nat-d {x = x} H (refl x)
  = ap (λ - → - ∙ H x) (∙-refl-r (H x ⁻¹)) ∙ (∙-sym-l (H x))
```

Whiskering
```agda
_∘ₗ_ : {A : type ℓ} {B : type ℓ'} {C : type ℓ''} {f g : A → B}
     → (h : B → C) → f ∼ g → h ∘ f ∼ h ∘ g
h ∘ₗ H = λ -  →  ap h (H -)
infix 70 _∘ₗ_

_∘ᵣ_ : {A : type ℓ} {B : type ℓ'} {C : type ℓ''} {g h : B → C}
     → g ∼ h → (f : A → B) → g ∘ f ∼ h ∘ f
H ∘ᵣ f = λ -  →  H (f -)
infix 70 _∘ᵣ_
```

Syntax sugars
```agda
_∼⟨_⟩_ :  {A : type ℓ} {𝓟 : A → type ℓ'} {g h : Π 𝓟}
       → (f : Π 𝓟) → f ∼ g → g ∼ h → f ∼ h
f ∼⟨ H ⟩ K = H ∙ₕ K
infixr 0 _∼⟨_⟩_

_□ : {A : type ℓ} {𝓟 : A → type ℓ'} (f : Π 𝓟) → f ∼ f
f □ = ht-refl f
infix  1 _□
```
