Basic settings for convenience
```agda
{-#  OPTIONS --without-K  #-}

module thesis-2 where

open import thesis-1 public

variable
  ℓ ℓ' ℓ'' ℓ''' : Level
```


Πtypes
```agda
Π :{A : type ℓ} → (A → type ℓ') → type (ℓ ⊔ ℓ')
Π {A = A} 𝓟 = (x : A) → 𝓟 x

-Π : (A : type ℓ) (𝓟 : A → type ℓ') → type (ℓ ⊔ ℓ')
-Π A 𝓟 = Π 𝓟
syntax -Π A (λ x → 𝓟x) = Π x ꞉ A , 𝓟x


id : {X : type ℓ} → X → X
id x = x


_∘_ : {X : type ℓ} {Y : type ℓ'} {𝓟 : (y : Y) → type ℓ''}
    → ((y : Y) → 𝓟 y) → (f : X → Y) → ((x : X) → 𝓟 (f x))
g ∘ f = λ x → g (f x)
infixl 70 _∘_
```


Σtypes
```agda
record Σ {A : type ℓ} (𝓟 : A → type ℓ') : type (ℓ ⊔ ℓ') where
    constructor
        _,_
    field
        pr₁ : A 
        pr₂ : 𝓟 pr₁
open Σ public
infixr 50 _,_

-Σ :  (A : type ℓ) (𝓟 : A → type ℓ') → type (ℓ ⊔ ℓ')
-Σ A 𝓟 = Σ 𝓟
syntax -Σ A (λ x → 𝓟x) = Σ x ꞉ A , 𝓟x


_×_ : type ℓ → type ℓ' → type (ℓ ⊔ ℓ')
A × B = Σ x ꞉ A , B
infixr 30 _×_

{-
Σelim : {A : 𝓤}  {𝓟 : A → 𝓤} {𝓠 : Σ 𝓟 → 𝓤}
     → ((x : A) (y : 𝓟 x) → 𝓠 (x , y))
     → ((x , y) : Σ 𝓟) → 𝓠 (x , y)
Σelim f (x , y) = f x y   -}
```



disjoint sum +
```agda
data _+_ (A : type ℓ) (B : type ℓ') : type (ℓ ⊔ ℓ') where
    inl : A → A + B
    inr : B → A + B
infixr 20 _+_
``` 


empty type 𝟘
```agda
data 𝟘 : 𝓤 where

𝟘elim : {𝓟 : 𝟘 → type ℓ} → (x : 𝟘) → 𝓟 x
𝟘elim ()

¬_ : type ℓ → type ℓ
¬ X = X → 𝟘
```

unit type 𝟙
```agda
data 𝟙 : 𝓤 where
    ⋆ : 𝟙

𝟙elim : {𝓟 : 𝟙 → type ℓ} → 𝓟 ⋆ → (x : 𝟙) → 𝓟 x
𝟙elim p ⋆ = p 
    
𝟚 : 𝓤
𝟚 = 𝟙 + 𝟙
pattern ₁ = inl ⋆
pattern ₂ = inr ⋆
-- 단순히 judgemental equality 를 추가하는 것을 넘어서
-- 패턴매칭 시 이 표기를 이용할 수 있게 허용한다.

const⋆ : {A : type ℓ} → A → 𝟙
const⋆ x = ⋆
```


우리의 유형론은 W-type 이라 불리는, 특정 꼴의 'initial algebra' 가 존재한다 선언해주는 유형건설자가 존재한다. 자세한 내용은 [UF] 의 5장을 참조... 그 하나의 예시로 아래의 자연수 대상이 있다.
(2 개의 constructor ; 각각 0-항수와 1-항수)


natural number object ℕ
```agda
data ℕ : 𝓤 where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
```

실제로 자연수대상이 되려면 같은 귀납가정으로 건설된 두 함수 f, g가 "같다"는 것을 보여야 한다. 이는 ＝ 를 다룬 후에 'up to propositional equality (up to homotopy)' 성립함을 쉽게 보일 수 있다. 자세히 다루지 않음.


identity types (path types, propositional equality)
```agda
data _＝_ {A : type ℓ} : A → A → type ℓ where
    refl : (x : A) → x ＝ x
infix 0 _＝_

{-
＝elim : {𝓟 : (x y : A) → x ＝ y → 𝓤}
      → ((x : A) → 𝓟 x x (refl x))
      → (x y : A) (p : x ＝ y) → 𝓟 x y p
＝elim F x .x (refl .x) = F x
-}
```



위의 path-type constructor 는 type 을 ∞-groupoid 로 만든다.
```agda
_∙_ : {X : type ℓ} {x y z : X} → x ＝ y → y ＝ z → x ＝ z
refl _ ∙ q = q
-- 여기서 agda 에서의 언더바의 두 번째 쓰임을 확인할 수 있다.
infixl 30 _∙_

_⁻¹ : {A : type ℓ} {x y : A} → x ＝ y → y ＝ x
refl _ ⁻¹ = refl _
infix 40 _⁻¹
sym = _⁻¹

∙-refl-l : {A : type ℓ} {x y : A}
         → (p : x ＝ y) → refl x ∙ p ＝ p
∙-refl-l (refl _) = refl _

∙-refl-r : {A : type ℓ} {x y : A}
         → (p : x ＝ y ) → p ∙ refl y ＝ p
∙-refl-r (refl _) = refl _

∙-sym-l : {A : type ℓ} {x y : A}
        → (p : x ＝ y ) → p ⁻¹ ∙ p ＝ refl y
∙-sym-l (refl _) = refl _

∙-sym-r : {A : type ℓ} {x y : A}
        → (p : x ＝ y ) → p ∙ p ⁻¹ ＝ refl x
∙-sym-r (refl _) = refl _

∙-assoc : {A : type ℓ} {x y z w : A}
        → (p : x ＝ y) (q : y ＝ z) (r : z ＝ w)
        → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙-assoc (refl _) q r = refl _

sym²~id : {A : type ℓ} {x y : A}
        → (p : x ＝ y) → sym (sym p) ＝ p
sym²~id (refl _) = refl _

sym∙ : {A : type ℓ} {x y z : A}
     → (p : x ＝ y) (q : y ＝ z)
     → sym (p ∙ q) ＝ sym q ∙ sym p
sym∙ (refl _) q = sym (∙-refl-r (q ⁻¹))
```



functions are groupoid functors
```agda
ap : {X : type ℓ} {Y : type ℓ'} {x x' : X}
   → (f : X → Y) → (x ＝ x') → f x ＝ f x'
ap f (refl _) = refl _

ap-refl : {X Y : type ℓ} {x : X}
        → (f : X → Y) → ap f (refl x) ＝ refl (f x)
ap-refl f = refl _

ap-∙ : {X : type ℓ} {Y : type ℓ'} {x y z : X}
     → (f : X → Y) (p : x ＝ y) (q : y ＝ z)
     → ap f (p ∙ q) ＝ ap f p ∙ ap f q
ap-∙ f (refl _) q = refl _

ap-sym : {X : type ℓ} {Y : type ℓ'} {x y : X}
       → (f : X → Y) (p : x ＝ y)
       → ap f (p ⁻¹) ＝ (ap f p) ⁻¹
ap-sym f (refl _) = refl _
```

id functor & composition of functors
```agda
ap-id : {X : type ℓ} {x y : X}
      → (p : x ＝ y) → ap id p ＝ p
ap-id (refl x) = refl _

ap-∘ : {X : type ℓ} {Y : type ℓ'} {Z : type ℓ''} {x y : X}
     → (g : Y → Z) (f : X → Y) (p : x ＝ y)
     → ap (g ∘ f) p ＝ (ap g (ap f p))
ap-∘ g f (refl x) = refl _
```



syntax sugars for ∙ and ap
```agda
_＝⟨_⟩_ : {A : type ℓ} {y z : A} (x : A) → x ＝ y → y ＝ z → x ＝ z
x ＝⟨ p ⟩ q = p ∙ q
infixr 0 _＝⟨_⟩_

_∎ : {A : type ℓ} (x : A) → x ＝ x
x ∎ = refl x
infix 1 _∎

ap₂ : {X : type ℓ} {Y : type ℓ'} {Z : type ℓ''} {x x' : X} {y y' : Y}
    → (F : X → Y → Z) → x ＝ x' → y ＝ y' → F x y ＝ F x' y'
ap₂ {x = x} {x' = x'} {y = y} {y' = y'} F p q
  = F x y  ＝⟨ ap _ p ⟩ 
    F x' y ＝⟨ ap _ q ⟩ 
    F x' y' ∎
```



tr - action of 1-path
유형족 𝓟 : X → 𝓤  은  presheaf (X,∙)ᵒᵖ → (𝓤,∘)
x ↦ 𝓟 x
∥p   ↓ trₚ
y ↦ 𝓟 y

```agda
tr : {A : type ℓ} {x y : A}
   → (𝓟 : A → type ℓ') → x ＝ y → 𝓟 x → 𝓟 y
tr 𝓟 (refl x) = id

-tr : {A : type ℓ} {x y : A} {𝓟 : A → type ℓ'}
    → x ＝ y → 𝓟 x → 𝓟 y
-tr (refl x) = id
syntax -tr p z = z ⟲ p


tr-∙ : {X : type ℓ} {x y z : X}
     → (𝓟 : X → type ℓ') (p : x ＝ y) (q : y ＝ z)
     → tr 𝓟 (p ∙ q) ＝ tr 𝓟 q ∘ tr 𝓟 p
tr-∙ 𝓟 (refl _) q = refl _

tr-∘ : {X : type ℓ} {Y : type ℓ'} {x x' : X}
     → (𝓟 : Y → type ℓ'') (f : X → Y) (p : x ＝ x')
     → tr (𝓟 ∘ f) p ＝ tr 𝓟 (ap f p)
tr-∘ 𝓟 f (refl _) = refl _

tr-const : {X : type ℓ} {Y : type ℓ'} {x x' : X}
         → (p : x ＝ x') (y : Y)
         → tr (λ - → Y) p y ＝ y
tr-const (refl _) y = refl y
```


Path on the total space
```agda
pathover : {A : type ℓ} (𝓟 : A → type ℓ') {a b : A}
        → (x : 𝓟 a) (y : 𝓟 b) (p : a ＝ b) → type ℓ'
pathover 𝓟 x y p = tr 𝓟 p x ＝ y

syntax pathover 𝓟 x y p = x ＝↑ y [ p ]over 𝓟
```


transport paths and maps
```agda
tr-fibmap : {X : type ℓ} {x y : X}
         → (𝓟 : X → 𝓤) (𝓠 : X → 𝓤) (p : x ＝ y) (f : 𝓟 x → 𝓠 x)
         → tr (λ - → 𝓟 - → 𝓠 -) p f ＝ (tr 𝓠 p) ∘ f ∘ (tr 𝓟 (p ⁻¹))
tr-fibmap 𝓟 𝓠 (refl _) f = refl f

tr-path-lfix : {X : type ℓ} {x y : X}
             → (s : X) (p : x ＝ y)
             → (r : s ＝ x) → tr (λ - → s ＝ -) p r ＝ r ∙ p
tr-path-lfix s (refl _) r = sym (∙-refl-r r)

tr-path-rfix : {X : type ℓ} {x y : X}
             → (t : X) (p : x ＝ y)
             → (r : x ＝ t) → tr (λ - → - ＝ t) p r ＝ (p ⁻¹) ∙ r
tr-path-rfix t (refl _) r = refl r

tr-path-btwmaps : {X : type ℓ} {Y : type ℓ'} {x y : X}
                → (f g : X → Y) (p : x ＝ y) (γ : f x ＝ g x)
                → tr (λ - → f - ＝ g -) p γ ＝ (ap f p) ⁻¹ ∙ γ ∙ (ap g p)
tr-path-btwmaps f g (refl _) γ = sym (∙-refl-r γ)
```


Sending path through section
```agda
apd : {X : type ℓ} {𝓟 : X → type ℓ'} {x y : X}
    → (f : Π 𝓟) (p : x ＝ y) → tr 𝓟 p (f x) ＝ f y
apd f (refl _) = refl (f _)

apd-const : {X : type ℓ} {Y : type ℓ'} {x y : X}
          → (f : X → Y) (p : x ＝ y)
          → apd f p ＝ (tr-const p (f x)) ∙ (ap f p)
apd-const f (refl _) = refl _
```
