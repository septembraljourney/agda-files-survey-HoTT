Import
```agda
{-#  OPTIONS --without-K  #-}

module thesis-3-equiv where

open import thesis-3-htpy public
```

Section and Retraction
```agda
has-sec : {A : type ℓ} {B : type ℓ'} (f : A → B) → type (ℓ ⊔ ℓ')
has-sec f = Σ (λ g → f ∘ g ∼ id)

has-ret : {A : type ℓ} {B : type ℓ'} (f : A → B) → type (ℓ ⊔ ℓ')
has-ret f = Σ (λ g → g ∘ f ∼ id)
```

Retraction of type
```agda

record _◁_  (A : type ℓ) (B : type ℓ') : type (ℓ ⊔ ℓ')  where
  constructor  ◁pf
  field
    ret : B → A
    retpf : has-sec (ret)

infix 0 _◁_
```
h-level, the concept measures the dimension in which the higher structure
of a given type become trivialized, is preserved with respect to retraction.
This will be introduced in the next section.


refl and composition of Retraction
```agda
{-◁refl : (X : 𝓤) → X ◁ X
◁refl X = ◁pf  id  (id , refl)

_◁∘_ : {X : 𝓤} {Y : 𝓤} {Z : 𝓤}
     → X ◁ Y → Y ◁ Z → X ◁ Z
◁pf r (s , H)  ◁∘  ◁pf r' (s' , H')
    = ◁pf  (r ∘ r')  ((s' ∘ s) , K)
    where
    K = r ∘ r' ∘ s' ∘ s   ∼⟨ (r ∘ₗ H') ∘ᵣ s ⟩
        r ∘ s  ∼⟨ H ⟩
        id □-}
```

syntax sugars for Retraction
```agda
{-_◁⟨_⟩_ : (X : 𝓤) {Y : 𝓤} {Z : 𝓤}  →  X ◁ Y  → Y ◁ Z  → X ◁ Z
X ◁⟨ R ⟩ R'  =  R ◁∘ R'

_◀ : (X : 𝓤) → X ◁ X
_◀ = ◁refl-}
```

invertible & equivalence
```agda
record  ivtbl  {A : type ℓ} {B : type ℓ'} (f : A → B) : type (ℓ ⊔ ℓ') where
  constructor  Ivtbl
  field
    inv : B → A
    inv-s : f ∘ inv ∼ id
    inv-r : inv ∘ f ∼ id


record  equiv  {A : type ℓ} {B : type ℓ'} (f : A → B) : type (ℓ ⊔ ℓ') where
  constructor Equiv
  field
    sec : B → A
    sec-h : f ∘ sec ∼ id
    ret : B → A
    ret-h : ret ∘ f ∼ id



record  _≅_  (A : type ℓ) (B : type ℓ') : type (ℓ ⊔ ℓ') where
  constructor ≅pf
  field
    ivt : A → B
    ivtpf : ivtbl ivt
infix  0 _≅_


record  _≃_  (A : type ℓ) (B : type ℓ') : type (ℓ ⊔ ℓ') where
  constructor ≃pf
  field
    eqv : A → B
    eqvpf : equiv eqv
infix  0 _≃_
```


Of course, ivtbl ⇒ equiv
```agda
ivtbl-equiv :  {A : type ℓ} {B : type ℓ'} {f : A → B}
            → (I : ivtbl f) → equiv f
ivtbl-equiv {f} (Ivtbl inv inv-s inv-r) = Equiv inv inv-s inv inv-r
```

Conversely, equivalence can be refined to invertibility proof. First we need to prove that if f is equiv with its section s and retraction r, s∼r
```agda
equiv-sec∼ret :  {A : type ℓ} {B : type ℓ'} {f : A → B}
              → (E : equiv f) →  equiv.sec(E) ∼ equiv.ret(E)
equiv-sec∼ret {f} (Equiv s S r R) = ((R ∘ᵣ s) ʰⁱ)  ∙ₕ  (r ∘ₗ S)
```

Now we get what we want:
```agda
equiv-ivtbl : {A : type ℓ} {B : type ℓ'} {f : A → B}
            → (E : equiv f) → ivtbl f
equiv-ivtbl {f = f} (Equiv s S r R) = Ivtbl s S ((H ∘ᵣ f) ∙ₕ R)
  where
  H = equiv-sec∼ret (Equiv s S r R)
```

Extracting inverse from equivalence data:
```agda
equiv-inv : {A : type ℓ} {B : type ℓ'} {f : A → B}
          → (E : equiv f) → (B → A)
equiv-inv E = ivtbl.inv (equiv-ivtbl E)

equiv-inv-equiv : {A : type ℓ} {B : type ℓ'} {f : A → B}
                → (E : equiv f) → equiv (equiv-inv E)
equiv-inv-equiv {f = f} E = ivtbl-equiv (Ivtbl f H (equiv.sec-h (E)))
  where
  H = equiv.sec(E) ∘ f   ∼⟨ equiv-sec∼ret(E) ∘ᵣ f ⟩
      equiv.ret(E) ∘ f   ∼⟨ equiv.ret-h E ⟩
      id  □
```


Rewriting the above logical equivalence for types:
```agda
≅-≃ : {A : type ℓ} {B : type ℓ'} → A ≅ B → A ≃ B
≅-≃ {A} {B} (≅pf ivt (Ivtbl inv inv-s inv-r))
  = ≃pf ivt (Equiv inv inv-s inv inv-r)

≃-≅ : {A : type ℓ} {B : type ℓ'} → A ≃ B → A ≅ B
≃-≅ {A} {B} (≃pf eqv  eqvpf) = ≅pf eqv (equiv-ivtbl eqvpf)


≃-eqv : {A : type ℓ} {B : type ℓ'} → A ≃ B → (A → B)
≃-eqv E = _≃_.eqv(E)

≃-inv :  {A : type ℓ} {B : type ℓ'} → A ≃ B → (B → A)
≃-inv E = ivtbl.inv (equiv-ivtbl (_≃_.eqvpf(E)))
```



Equivalence preserves higher structures
```agda
ASSOC : {X : type ℓ} {x1 x2 x3 x4 x5 x6 : X}
      → (p1 : x1 ＝ x2) (p2 : x2 ＝ x3) (p3 : x3 ＝ x4) (p4 : x4 ＝ x5) (p5 : x5 ＝ x6)
      → (p1 ∙ p2) ∙ p3 ∙ (p4 ∙ p5) ＝ p1 ∙ (p2 ∙ p3 ∙ p4) ∙ p5
ASSOC (refl _) (refl _) p3 p4 p5 = sym (∙-assoc p3 p4 p5)

≅-pathspace : (A : type ℓ) (B : type ℓ') → (I : A ≅ B) → (x y : A)
            → ((x ＝ y) ≅ (_≅_.ivt(I) x ＝ _≅_.ivt(I) y))
≅-pathspace A B (≅pf f (Ivtbl fⁱ S R)) x y
  = ≅pf (ap f) (Ivtbl i s r)
  where
  i : f x ＝ f y  →  x ＝ y
  i p = (R x) ⁻¹ ∙ (ap fⁱ p) ∙ (R y)
  s : ap f ∘ i ∼ id
  s q =  ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y)
               ＝⟨ ∙-refl-r ( ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y)) ⁻¹ ⟩
         (refl _) ∙  ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y) ∙ (refl _)
               ＝⟨ ap₂ (λ - ~ → - ∙ _ ∙ ~) (∙-sym-l (S (f x)) ⁻¹) (∙-sym-l (S (f y)) ⁻¹) ⟩
         (S (f x) ⁻¹ ∙ S (f x)) ∙ ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y) ∙ (S (f y) ⁻¹ ∙ S (f y))
               ＝⟨ ASSOC (S (f x) ⁻¹) (S (f x)) (ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y)) (S (f y) ⁻¹) (S (f y)) ⟩
         S (f x) ⁻¹ ∙  (S (f x) ∙ ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y) ∙ S (f y) ⁻¹) ∙ S (f y)
              ＝⟨ ap (λ - →  S (f x) ⁻¹ ∙  (S (f x) ∙ - ∙ S (f y) ⁻¹) ∙ S (f y))  (sym (ap-id (ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y)))) ⟩
         S (f x) ⁻¹ ∙ (S (f (id x)) ∙ ap id (ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y)) ∙ S (f (id y)) ⁻¹) ∙ S (f y)
              ＝⟨  ap (λ - → S (f x) ⁻¹ ∙ - ∙ S (f y)) (ht-nat-u S (ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y))) ⟩
         S (f x) ⁻¹ ∙ ap (f ∘ fⁱ) (ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y)) ∙ S (f y)
               ＝⟨ ap (λ - → S (f x) ⁻¹ ∙ - ∙ S (f y)) (ap-∘ f fⁱ (ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y))) ⟩
         S (f x) ⁻¹ ∙ (ap f (ap fⁱ (ap f (R x ⁻¹ ∙ ap fⁱ q ∙ R y)))) ∙ S (f y)
               ＝⟨ ap (λ - → S (f x) ⁻¹ ∙ ap f - ∙ S (f y)) (sym (ap-∘ fⁱ f _)) ⟩
         S (f x) ⁻¹ ∙ ap f (ap (fⁱ ∘ f) (R x ⁻¹ ∙ ap fⁱ q ∙ R y)) ∙ S (f y)
               ＝⟨ ap (λ - → S (f x) ⁻¹ ∙ ap f - ∙ S (f y)) (sym (ht-nat-u R _)) ⟩
         S (f x) ⁻¹ ∙ ap f (R x ∙ ap id (R x ⁻¹ ∙ ap fⁱ q ∙ R y) ∙ R y ⁻¹) ∙ S (f y)
               ＝⟨ ap (λ - → S (f x) ⁻¹ ∙ ap f (R x ∙ - ∙ R y ⁻¹) ∙ S (f y)) (ap-id _) ⟩
         S (f x) ⁻¹ ∙ ap f (R x ∙ (R x ⁻¹ ∙ ap fⁱ q ∙ R y) ∙ R y ⁻¹) ∙ S (f y)
              ＝⟨ ap (λ - → S (f x) ⁻¹ ∙ ap f - ∙ S (f y)) (sym (ASSOC (R x) (R x ⁻¹) (ap fⁱ q) (R y) (R y ⁻¹)))⟩
         S (f x) ⁻¹ ∙ ap f ((R x ∙ R x ⁻¹) ∙ ap fⁱ q ∙ (R y ∙ R y ⁻¹)) ∙ S (f y)
              ＝⟨ ap (λ - → S (f x) ⁻¹ ∙ ap f - ∙ S (f y))  (ap₂ (λ - ~ → - ∙ _ ∙ ~) (∙-sym-r (R _)) (∙-sym-r (R _))) ⟩
         S (f x) ⁻¹ ∙ ap f (ap fⁱ q ∙ (refl _)) ∙ S (f y)
              ＝⟨ ap (λ - → S (f x) ⁻¹ ∙ ap f - ∙ S (f y)) (∙-refl-r _) ⟩
         S (f x) ⁻¹ ∙ ap f (ap fⁱ q) ∙ S (f y)
              ＝⟨ ap (λ - → S (f x) ⁻¹ ∙ - ∙ S (f y)) (sym (ap-∘ f fⁱ q)) ⟩
         S (f x) ⁻¹ ∙ ap (f ∘ fⁱ) q ∙ S (f y)
              ＝⟨ ap (λ - → S (f x) ⁻¹ ∙ - ∙ S (f y)) (sym (ht-nat-u S _)) ⟩
         S (f x) ⁻¹ ∙ (S (f x) ∙ ap id q ∙ S (f y) ⁻¹) ∙ S (f y)
              ＝⟨ sym (ASSOC (S (f x) ⁻¹) (S (f x)) (ap id q) (S (f y) ⁻¹) (S (f y))) ⟩
         (S (f x) ⁻¹ ∙ S (f x)) ∙ ap id q ∙ (S (f y) ⁻¹ ∙ S (f y))
               ＝⟨  ap₂ (λ - ~ → - ∙ _ ∙ ~) (∙-sym-l (S (f x))) (∙-sym-l (S (f y))) ⟩
         ap id q ∙ refl _   ＝⟨ ∙-refl-r (ap id q) ∙ ap-id q ⟩
         q ∎

  r : i ∘ ap f ∼ id
  r q  =  R x ⁻¹ ∙ ap fⁱ (ap f q) ∙ R y  ＝⟨ ap (λ - → R x ⁻¹ ∙ - ∙ R y) (sym (ap-∘ fⁱ f q)) ⟩
       R x ⁻¹ ∙ ap (fⁱ ∘ f) q ∙ R y ＝⟨ ap (λ - → R x ⁻¹ ∙ - ∙ R y) (sym (ht-nat-u R q)) ⟩
       R x ⁻¹ ∙ (R x ∙ ap id q ∙ R y ⁻¹) ∙ R y ＝⟨ sym (ASSOC (R x ⁻¹) (R x) (ap id q) (R y ⁻¹) (R y)) ⟩
       (R x ⁻¹ ∙ R x) ∙ ap id q ∙ (R y ⁻¹ ∙ R y) ＝⟨ ap₂ (λ - ~ → - ∙ _ ∙ ~) (∙-sym-l (R x)) (∙-sym-l (R y)) ⟩
       ap id q ∙ refl _ ＝⟨ ∙-refl-r (ap id q) ∙ ap-id q ⟩
       q ∎


≃-pathspace : (A B : type ℓ) → (e : A ≃ B) → (x y : A)
  → ((x ＝ y) ≃ (_≃_.eqv(e) x ＝ _≃_.eqv(e) y))
≃-pathspace A B e x y = ≅-≃ (≅-pathspace A B I x y)
  where
  I = ≃-≅ e
```
