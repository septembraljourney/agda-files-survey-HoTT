Import
```agda
{-#  OPTIONS --rewriting --without-K  #-}

module thesis-5 where

open import thesis-4-hit public
open import thesis-3-hlvl public
```


There is a type constructor which forgets higher structures
and preserves paths below the dimension k, called k-truncation.

n-th homotopy group is defined as set-level truncation of n-dimensional loop space
We actually prove more stronger statement (base ＝ base) ≅ ℤ
that is, loop space is already has no interesting higher structure before we truncate it to a set.

Define cover
```agda
Ω¹S¹ = base ＝ base

loop^_ : ℤ → Ω¹S¹
loop^ pos 0 = refl base
loop^ pos (suc n) = (loop^ (pos n)) ∙ loop
loop^ negsuc 0 = loop ⁻¹
loop^ negsuc (suc n) = (loop^ (negsuc n)) ∙ loop ⁻¹

--universial cover of S¹
cover : S¹ → 𝓤
cover = S¹rec  𝓤  ℤ  (ua succ-≃)

loopact＝succ : tr cover loop ＝ succℤ
loopact＝succ
  = tr cover loop ＝⟨ tr-∘ id cover loop ⟩
    tr id (ap cover loop) ＝⟨ ap (λ - → tr id -) (S¹rec-comp-loop 𝓤 ℤ (ua succ-≃)) ⟩
    tr id (ua succ-≃) ＝⟨ tr-ua succ-≃ ⟩
    succℤ ∎

loop⁻¹act＝pred : tr cover (loop ⁻¹) ＝ predℤ
loop⁻¹act＝pred
  = tr cover (loop ⁻¹) ＝⟨ tr-∘ id cover (loop ⁻¹) ⟩
  tr id (ap cover (loop ⁻¹)) ＝⟨ ap (λ - → tr id -) (ap-sym cover loop) ⟩
  tr id ((ap cover loop)⁻¹) ＝⟨ ap (λ - → tr id (- ⁻¹)) (S¹rec-comp-loop 𝓤 ℤ (ua succ-≃)) ⟩
  tr id ((ua succ-≃)⁻¹) ＝⟨ ap (λ - → tr id -) (sym (ua-sym (succ-≃))) ⟩
  tr id (ua (≃sym succ-≃)) ＝⟨ tr-ua (≃sym succ-≃) ⟩
  predℤ ∎
```


There is no way to define the required function (base ＝ base) → ℤ.
Instead, we make one end point free and use transport.
```agda
encode : (z : S¹) → (base ＝ z → cover z)
encode z p = tr cover p (pos 0)
```
Now we construct the fiberwise inverse of encode
```agda
decode : (z : S¹) → (cover z → base ＝ z)
decode = S¹elim
           𝓟
           loop^_
           loop^toloop^-over-loop
  where
  𝓟 = (λ z → cover z → base ＝ z)
  loop^toloop^-over-loop : loop^_ ＝↑ loop^_ [ loop ]over 𝓟
  loop^toloop^-over-loop
    = tr 𝓟 loop loop^_ ＝⟨ tr-fibmap cover (_＝_ base) loop loop^_ ⟩
      tr (_＝_ base) loop ∘ loop^_ ∘ tr cover (loop ⁻¹) ＝⟨ ap (λ - → tr (_＝_ base) loop ∘ loop^_ ∘ -) loop⁻¹act＝pred ⟩
      tr (_＝_ base) loop ∘ loop^_ ∘ predℤ ＝⟨ ap (λ - → - ∘ loop^_ ∘ predℤ) (fext (tr-path-lfix base loop)) ⟩
      (λ - → - ∙ loop) ∘ loop^_ ∘ predℤ ＝⟨ fext H ⟩
      loop^_ ∎
    where
    H : (λ - → - ∙ loop) ∘ loop^_ ∘ predℤ   ∼   loop^_
    H (pos 0) = ∙-sym-l loop
    H (pos (suc n)) = refl _
    H (negsuc x) = (loop^ negsuc x) ∙ loop ⁻¹ ∙ loop ＝⟨ ∙-assoc (loop^ negsuc x) (loop ⁻¹) loop ⟩
                   (loop^ negsuc x) ∙ (loop ⁻¹ ∙ loop) ＝⟨ ap (λ - → (loop^ negsuc x) ∙ -) (∙-sym-l loop) ⟩
                   (loop^ negsuc x) ∙ (refl _) ＝⟨ ∙-refl-r (loop^ negsuc x) ⟩
                   (loop^ negsuc x) ∎
```

Now it remains to prove that encode and decode indeed constitute inverse pair on each fiber of S¹
```agda
encode-decode : (z : S¹) → (encode z) ∘ (decode z) ∼ id
encode-decode = S¹elim
                   𝓟
                   htpy-base
                   (fext (λ n → set→set' ℤ-is-set _ _ _ _))
  where
  𝓟 = (λ z → encode z ∘ decode z ∼ id)
  htpy-base : (m : ℤ) → tr cover (loop^ m) (pos 0) ＝ m
  htpy-base (pos 0) = refl (pos 0)
  htpy-base (pos (suc n))
            = tr cover ((loop^ pos n) ∙ loop) (pos 0)  ＝⟨ ap (λ - → - (pos 0)) (tr-∙ cover (loop^ pos n) loop) ⟩
              tr cover loop (tr cover (loop^ pos n) (pos 0)) ＝⟨ ap (λ - → tr cover loop -) (htpy-base (pos n)) ⟩
              tr cover loop (pos n) ＝⟨ ap (λ - → - (pos n)) loopact＝succ ⟩
              pos (suc n) ∎
  htpy-base (negsuc 0)
            = tr cover (loop ⁻¹) (pos 0) ＝⟨ ap (λ - → - (pos 0)) loop⁻¹act＝pred ⟩
              (negsuc 0) ∎
  htpy-base (negsuc (suc n))
            = tr cover ((loop^ negsuc n) ∙ loop ⁻¹) (pos 0) ＝⟨ ap (λ - → - (pos 0)) (tr-∙ cover (loop^ negsuc n) (loop ⁻¹)) ⟩
              tr cover (loop ⁻¹) (tr cover (loop^ negsuc n) (pos 0)) ＝⟨ ap (λ - → tr cover (loop ⁻¹) -) (htpy-base (negsuc n)) ⟩
              tr cover (loop ⁻¹) (negsuc n) ＝⟨ ap (λ - → - (negsuc n)) loop⁻¹act＝pred ⟩
              negsuc (suc n) ∎
```
The last argument is a term of loop⁎(htpy-base)＝htpy-base  in encode(base) ∘ decode(base) ∼ id.
By fext this can be constructed by giving a term of loop⁎(htpy-base)∼htpy-base, that is,
a term of (n : ℤ) → loop⁎(htpy-base) n ＝ htpy-base n
where each end point is a path in ℤ. That is, it's a matter of giving a 2-path between parallel 1 paths.
This can be trivially done by the fact that ℤ is a set.


Now we complete our goal
```agda
decode-encode : (z : S¹) → (decode z) ∘ (encode z) ∼ id
decode-encode base (refl base) = refl (refl base)


S¹-fiberwise-eqv : (z : S¹) → (base ＝ z) ≃ (cover z)
S¹-fiberwise-eqv z = ≅-≃ (≅pf (encode z) (Ivtbl (decode z) (encode-decode z) (decode-encode z)))
```
It can be shown that a fiberwise equivalence induces their total space equivalence.
And it is easy to prove that for any type A and a : A,
Σ (x : A) , a ＝ x  is contractible.
Hence the above term (S¹-fiberwise-eqv) shows that the total space of cover is contractible.
∴ cover is the universial cover.

```agda
Ω¹S¹≃ℤ : Ω¹S¹ ≃ ℤ
Ω¹S¹≃ℤ = S¹-fiberwise-eqv base
```
