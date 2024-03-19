Import
```agda
{-#  OPTIONS --without-K  #-}

module thesis-3-hlvl where

open import thesis-3-equiv public
```

contractible - trivially inhabited
```agda
contr : type ℓ → type ℓ
contr A = Σ c ꞉ A , (Π x ꞉ A , (c ＝ x))

-- a contractible type is inhabited by its center
center : {A : type ℓ} → contr A → A
center C = pr₁ C

𝟙-contr : contr 𝟙
𝟙-contr = ⋆ , λ {⋆ → refl ⋆} --inline pattern matching using brackets!

contr-closed-above : {A : type ℓ} → (contr A) → ((x y : A) → contr (x ＝ y))
contr-closed-above (c , H) x y
  = ((H x) ⁻¹ ∙ H y) , λ { (refl x) → ∙-sym-l (H x)}
```


general h-level , proposition, set
h-level measures the level of dimension where the higher structure of a type becomes trivial.
```agda
_has-hlv_ : type ℓ → ℕ → type ℓ
A has-hlv 0 = contr A
A has-hlv suc n = (x y : A) → (x ＝ y) has-hlv n

prop : type ℓ → type ℓ
prop A = A has-hlv 1

𝟘-prop : prop 𝟘
𝟘-prop = λ x ()

set : type ℓ → type ℓ
set A = A has-hlv 2

set' : type ℓ → type ℓ
set' A = (x y : A) → (p q : x ＝ y) → p ＝ q

set→set' : {A : type ℓ} → set A → set' A
set→set' sA x y p q = pr₁ (sA x y p q)

set'→set : {A : type ℓ} → set' A → set A
set'→set sA' x y p q = contr-closed-above  below-contr p q
  where
  below-contr : contr (x ＝ y)
  below-contr = p , (sA' x y p)

```



Properties of h-level
```agda
hlv-closed-above : (n : ℕ) {A : type ℓ} → (A has-hlv n) → (A has-hlv (suc n))
hlv-closed-above 0 H = contr-closed-above H
hlv-closed-above  (suc n) H x y = IH {T = (x ＝ y)} (H x y)
  where
  IH : {T : type ℓ} → (T has-hlv n) → (T has-hlv (suc n))
  IH = hlv-closed-above n


𝟙-prop : prop 𝟙
𝟙-prop = hlv-closed-above 0 𝟙-contr

𝟙-is-set : set 𝟙
𝟙-is-set = hlv-closed-above 1 𝟙-prop

𝟘-is-set : set 𝟘
𝟘-is-set = hlv-closed-above 1 𝟘-prop



contr-closed-ret : {A : type ℓ} {B : type ℓ'} → A ◁ B → contr B → contr A
contr-closed-ret {A = A} (◁pf r (s , H)) (b , C) = r b , K
  where
  K : (x : A) → r b ＝ x
  K x = r b ＝⟨ ap r (C (s x)) ⟩
        r (s x) ＝⟨ H x ⟩
        x ∎

{-
◁-closed-above : {A : type ℓ} {B : type ℓ'}
               → ((◁pf r (s , H)) : A ◁ B) → (x y : A) → (x ＝ y) ◁ (s x ＝ s y)
◁-closed-above (◁pf r (s , H)) x y =
  ◁pf ((λ - → (H x) ⁻¹ ∙ - ∙ (H y)) ∘ ap r)
      ((ap s) , K)
    where
    K : (p : x ＝ y) → H x ⁻¹ ∙ ap r (ap s p) ∙ H y ＝ p
    K p = H x ⁻¹ ∙ ap r (ap s p) ∙ H y  ＝⟨ ap (λ - → (H x) ⁻¹ ∙ - ∙ (H y)) (sym (ap-∘ r s p)) ⟩
          H x ⁻¹ ∙ ap (r ∘ s) p ∙ H y   ＝⟨ ht-nat-d H p ⟩
          ap id p ＝⟨ ap-id p ⟩
          p ∎
아래의 path induction 을 안쓰는 증명 -}

◁-closed-above : {A : type ℓ} {B : type ℓ'}
               → ((◁pf r (s , H)) : A ◁ B) → (x y : A) → (x ＝ y) ◁ (s x ＝ s y)
◁-closed-above (◁pf r (s , H)) x y =
  ◁pf ((λ - → (H x) ⁻¹ ∙ - ∙ (H y)) ∘ ap r)
      ((ap s) , K)
    where
    K : (p : x ＝ y) → H x ⁻¹ ∙ ap r (ap s p) ∙ H y ＝ p
    K (refl x) = (ap (λ - → - ∙ H x) (∙-refl-r (H x ⁻¹))) ∙ (∙-sym-l (H x))




hlv-closed-ret : (n : ℕ) {A : type ℓ} {B : type ℓ'}
               → A ◁ B → (B has-hlv n) → (A has-hlv n)
hlv-closed-ret zero R hB = contr-closed-ret R hB
hlv-closed-ret (suc n) {A = A} {B = B} R hB  x y = IH (◁-closed-above R x y) (hB (s x) (s y))
  where
  IH = hlv-closed-ret n
  s : A → B
  s = pr₁ (_◁_.retpf R)
```



Now we define the type of integers ℤ with succesor and predecessor operations
and prove that ℤ is set.
```agda
data ℤ : 𝓤 where
 pos : ℕ → ℤ
 negsuc : ℕ → ℤ

succℤ : ℤ → ℤ
succℤ (pos x) = pos (suc x)
succℤ (negsuc 0) = pos 0
succℤ (negsuc (suc x)) = negsuc x

predℤ : ℤ → ℤ
predℤ (pos 0) = negsuc 0
predℤ (pos (suc x)) = pos x
predℤ (negsuc x) = negsuc (suc x)

succ-sec : predℤ ∘ succℤ ∼ id
succ-sec (pos x) = refl _
succ-sec (negsuc 0) = refl _
succ-sec (negsuc (suc x)) = refl _

succ-ret : succℤ ∘ predℤ ∼ id
succ-ret (pos 0) = refl _
succ-ret (pos (suc x)) = refl _
succ-ret (negsuc x) = refl _

succ-≅ : ℤ ≅ ℤ
succ-≅ = ≅pf succℤ (Ivtbl predℤ succ-ret succ-sec)

succ-≃ : ℤ ≃ ℤ
succ-≃ = ≅-≃ succ-≅

-- Of course, one can define the integer by ℕ + ℕ with suitable operations on it.
-- Indeed, we can make equivalence between them
ℤ→ : ℤ → ℕ + ℕ
ℤ→ (pos x) = inr x
ℤ→ (negsuc x) = inl x

ℤ← : ℕ + ℕ → ℤ
ℤ← (inl x) = negsuc x
ℤ← (inr x) = pos x

ℤ≅ℕ+ℕ : ℤ ≅ ℕ + ℕ
ℤ≅ℕ+ℕ = ≅pf ℤ→ (Ivtbl ℤ← H K)
  where
  H : (x : ℕ + ℕ) → ℤ→ (ℤ← x) ＝ x
  H (inl x) = refl (inl x)
  H (inr x) = refl (inr x)
  K : (x : ℤ) → ℤ← (ℤ→ x) ＝ x
  K (pos x) = refl (pos x)
  K (negsuc x) = refl (negsuc x)
```

To prove that ℤ is a set, it will be suffice to prove that ℕ is a set and sets are closed under +.
To prove that ℕ is a set, we define
auxilary 'binary predicate' over ℕ:
```agda
ℕeq : ℕ → ℕ → 𝓤
ℕeq 0 0 = 𝟙
ℕeq 0 (suc n) = 𝟘
ℕeq (suc m) 0 = 𝟘
ℕeq (suc m) (suc n) = ℕeq m n

ℕeq-prop : (m n : ℕ) → prop (ℕeq m n)
ℕeq-prop zero zero = 𝟙-prop
ℕeq-prop zero (suc n) = 𝟘-prop
ℕeq-prop (suc m) zero = 𝟘-prop
ℕeq-prop (suc m) (suc n) = ℕeq-prop m n


ℕeq← : (m n : ℕ) → m ＝ n → ℕeq m n
ℕeq← 0 0 (refl _) = ⋆
ℕeq← (suc m) (suc m) (refl _) = ℕeq← m m (refl m)

ℕeq→ : (m n : ℕ) → ℕeq m n → m ＝ n
ℕeq→ 0 0 ⋆ = refl 0
ℕeq→ 0 (suc n) = λ ()
ℕeq→ (suc m) 0 = λ ()
ℕeq→ (suc m) (suc n) = (ap suc) ∘ IH
  where
  IH : ℕeq m n → m ＝ n
  IH = ℕeq→ m n

ℕeq←suc : (m n : ℕ) → (ℕeq← (suc m) (suc n)) ∘ (ap suc) ∼ ℕeq← m n
ℕeq←suc m m (refl m) = refl (ℕeq← m m (refl m))


ℕeq≅ : (m n : ℕ) → (m ＝ n) ≅ ℕeq m n
ℕeq≅ = λ m n → ≅pf (ℕeq← m n) (Ivtbl (ℕeq→ m n) (S m n) (R m n))
  where
  S : (m n : ℕ) → (ℕeq← m n) ∘ (ℕeq→ m n) ∼ id
  S 0 0 ⋆ = refl ⋆
  S 0 (suc n) = λ ()
  S (suc m) 0 = λ ()
  S (suc m) (suc n) = ((ℕeq←suc m n) ∘ᵣ (ℕeq→ m n)) ∙ₕ (S m n)

  R : (m n : ℕ) → (ℕeq→ m n) ∘ (ℕeq← m n) ∼ id
  R 0 0 (refl 0) = refl (refl 0)
  R (suc m) (suc m) (refl (suc m)) = ap (ap suc) (R m m (refl m))


≅-◁ : {A : type ℓ} {B : type ℓ'} → A ≅ B → A ◁ B
≅-◁ (≅pf ivt (Ivtbl inv inv-s inv-r)) = ◁pf inv (ivt , inv-r)


ℕ-is-set : set ℕ
ℕ-is-set m n = hlv-closed-ret 1 RET (ℕeq-prop m n)
  where
  RET : (m ＝ n) ◁ ℕeq m n
  RET = ≅-◁ (ℕeq≅ m n)

```



Now we prove that set is closed w.r.t +
```agda

+-disjoint : {A : type ℓ} {B : type ℓ'} → (a : A) (b : B) → ¬ (inl a ＝ inr b)
+-disjoint {A = A} {B = B} a b p = tr 𝓟 p ⋆
  where
  𝓟 : A + B → 𝓤
  𝓟 (inl x) = 𝟙
  𝓟 (inr y) = 𝟘

{- cumulativity 는 Agda 에서 기본적으로 가정되지 않는다... 리프팅을 정의하기보다는 우회로를 찾기!
+eq : {A : type ℓ} {B : type ℓ'} → (x y : A + B) → type {!!}
+eq (inl a) (inl a') = a ＝ a'
+eq (inl a) (inr b) = 𝟘
+eq (inr b) (inl a) = 𝟘
+eq (inr b) (inr b') = b ＝ b'  -}

+-pointed-pr-l : {A : type ℓ} {B : type ℓ'} → A → A + B → A
+-pointed-pr-l a₀ (inl a) = a
+-pointed-pr-l a₀ (inr b) = a₀

+-pointed-pr-r : {A : type ℓ} {B : type ℓ'} → B → A + B → B
+-pointed-pr-r b₀ (inl a) = b₀
+-pointed-pr-r b₀ (inr b) = b


------
+eq : {A : type ℓ} {B : type ℓ'}
  → (x y : A + B) (p : x ＝ y) → (Σ a ꞉ A , (Σ a' ꞉ A , (a ＝ a'))) + (Σ b ꞉ B , (Σ b' ꞉ B , (b ＝ b')))
+eq (inl a) (inl a) (refl (inl a)) = inl (a , a , refl a)
+eq (inr b) (inr b) (refl (inr b)) = inr (b , b , refl b)
------

apinlⁱ : {A : type ℓ} {B : type ℓ'}
       → (a : A) → (x : A + B) → (inl a ＝ x) → (a ＝ (+-pointed-pr-l a) x)
apinlⁱ {A = A} {B = B} a (inl a) (refl (inl a)) = refl a

apinrⁱ : {A : type ℓ} {B : type ℓ'}
       → (b : B) → (x : A + B) → (inr b ＝ x) → (b ＝ (+-pointed-pr-r b) x)
apinrⁱ {A = A} {B = B} b (inr b) (refl (inr b)) = refl b


aux-l : {A : type ℓ} {B : type ℓ'}
      → (a : A) (x : A + B) (q : inl a ＝ x) → x ＝ inl (+-pointed-pr-l a x)
aux-l a (inl a') q = refl (inl a')
aux-l a (inr b) q = 𝟘elim (+-disjoint a b q)

inl-emb :  {A : type ℓ} {B : type ℓ'}
        → (a a' : A) → (inl {A = A} {B = B} a ＝ inl a') ≅ (a ＝ a')
inl-emb {A = A} {B = B} a a'
  = ≅pf (apinlⁱ a (inl a'))
        (Ivtbl (ap inl)
               S
               λ q → (R (inl a') q) ∙ (∙-refl-r q))
  where
  S : apinlⁱ {A = A} {B = B} a (inl a') ∘ ap inl ∼ id
  S (refl .a) = refl (refl a)

  R : (x : A + B) (q : inl a ＝ x) → ap (inl {A = A} {B = B}) (apinlⁱ a x q) ＝ q ∙ aux-l a x q
  R .(inl a) (refl .(inl a)) = refl _


aux-r : {A : type ℓ} {B : type ℓ'} → (b : B) (x : A + B) (q : inr b ＝ x) → x ＝ inr (+-pointed-pr-r b x)
aux-r b (inr y) q = refl (inr y)

inr-emb :  {A : type ℓ} {B : type ℓ'} → (b b' : B) → (inr {A = A} {B = B} b ＝ inr b') ≅ (b ＝ b')
inr-emb {A = A} {B = B} b b' = ≅pf (apinrⁱ b (inr b')) (Ivtbl (ap inr) S λ q → R (inr b') q ∙ ∙-refl-r q)
  where
  S : apinrⁱ {A = A} {B = B} b (inr b') ∘ ap inr ∼ id
  S (refl b) = refl (refl b)

  R : (x : A + B) (q : inr b ＝ x) → ap (inr {A = A} {B = B}) (apinrⁱ b x q) ＝ q ∙ aux-r b x q
  R (inr b) (refl (inr b)) = refl _



set-closed-+ : {A : type ℓ} {B : type ℓ'} → set A → set B → set (A + B)
set-closed-+ sA sB (inl a) (inl a') = hlv-closed-ret 1 (≅-◁ (inl-emb a a')) (sA a a')
set-closed-+ sA sB (inl a) (inr b) = λ x ()
set-closed-+ sA sB (inr b) (inl a) = λ x ()
set-closed-+ sA sB (inr b) (inr b') = hlv-closed-ret 1 (≅-◁ (inr-emb b b')) (sB b b')


ℤ-is-set : set ℤ
ℤ-is-set = hlv-closed-ret 2 (≅-◁ ℤ≅ℕ+ℕ) (set-closed-+ ℕ-is-set ℕ-is-set)
```




