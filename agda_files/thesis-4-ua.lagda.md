Import
```agda
{-#  OPTIONS --without-K  #-}

module thesis-4-ua where

open import thesis-4-fext public
```


Definition of univalence
Note that the type A ＝ B , the path in the universe "type ℓ",
resides in the universe "type (lsuc l)" since "type ℓ : type (lsuc l)".
```agda
tr-id : {A B : type ℓ} → A ＝ B → (A → B)
tr-id = tr id

＝-≅ : {A B : type ℓ} → A ＝ B → A ≅ B
＝-≅ p = (≅pf (tr-id p)
      (Ivtbl (tr-id (p ⁻¹)) H K))
  where     -- (tr∙ (𝑖𝑑 (type ℓ)) (p ⁻¹) p) ⁻¹
  H : tr-id p ∘ tr-id (p ⁻¹) ∼ id
  H = (tr (id) p ∘ tr (id) (p ⁻¹))   ∼⟨ happ (sym (tr-∙ (id) (sym p) p) ) ⟩
        tr (id) (p ⁻¹ ∙ p)           ∼⟨ happ (ap (\ - → tr id -) (∙-sym-l p)) ⟩
        id □

  K :  tr (id) (p ⁻¹) ∘ tr (id) p ∼ id
  K = (tr (id) (p ⁻¹) ∘ tr (id) p)   ∼⟨ happ (sym (tr-∙ (id) p (sym p)) ) ⟩
        tr (id) (p ∙ p ⁻¹)    ∼⟨  happ (ap (\ - →  tr (id) -) (∙-sym-r p)) ⟩
        id □

＝-≃ : {A B : type ℓ} → A ＝ B → A ≃ B
＝-≃ = ≅-≃ ∘ ＝-≅
uaⁱ = ＝-≃

postulate
  UA : {A B : 𝓤} → equiv (＝-≃ {A = A} {B = B})
```


Gadgets for univalence
```agda
UA-ivtbl : {A B : 𝓤} → ivtbl (＝-≃ {A = A} {B = B})
UA-ivtbl = equiv-ivtbl (UA)

ua : {A B : 𝓤} → A ≃ B → A ＝ B
ua = ivtbl.inv (UA-ivtbl)

ua-s : {A B : 𝓤} → (uaⁱ {A = A} {B = B}) ∘ (ua {A = A} {B = B}) ∼ id
ua-s = ivtbl.inv-s (UA-ivtbl)

ua-r : {A B : 𝓤} → (ua {A = A} {B = B}) ∘ (uaⁱ {A = A} {B = B}) ∼ id
ua-r = ivtbl.inv-r (UA-ivtbl)
```


Basic properties of ua

```agda
tr-ua : {X Y : 𝓤} (E : X ≃ Y)  →  tr-id (ua E) ＝ (_≃_.eqv E)
tr-ua = _≃_.eqv  ∘ₗ  (ua-s)  -- ua-s : uaⁱ ∘ ua ∼ id  ;  eqv ∘ uaⁱ ≐ tr-id    ∵ uaⁱ(p) ≐  (tr-id(p), tr-id(p⁻¹), ...)

≃sym : {X : type ℓ} {Y : type ℓ'} → X ≃ Y → Y ≃ X
≃sym (≃pf eqv eqvpf) = ≃pf (equiv-inv eqvpf) (equiv-inv-equiv eqvpf)

＝-≃-sym : {X Y : 𝓤} → (p : X ＝ Y) → ＝-≃ (sym p) ＝ ≃sym (＝-≃ p)
＝-≃-sym (refl _) = refl _

ua-sym : {X Y : 𝓤} → (E : X ≃ Y) → ua (≃sym E) ＝ sym (ua E)
ua-sym E
 = ua (≃sym E)        ＝⟨ ap (λ - → ua (≃sym -)) (sym (ua-s E)) ⟩
   ua (≃sym (＝-≃ (ua E)))  ＝⟨ ap ua (sym (＝-≃-sym (ua E))) ⟩
   ua (＝-≃ (sym (ua E)))   ＝⟨ ua-r (sym (ua E)) ⟩
   sym (ua E)  ∎

```
