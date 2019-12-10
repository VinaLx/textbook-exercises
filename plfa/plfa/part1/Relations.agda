module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _∎)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (+-comm; ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤;
   *-zeroʳ; +-*-suc; +-suc; +-identityʳ)

open import plfa.part1.Naturals

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ .0 n p z≤n = z≤n
*-monoˡ-≤ (suc m) (suc n) p (s≤s m≤n) = +-monoʳ-≤ p (*-monoˡ-≤ m n p m≤n)

*-monoʳ-≤ : ∀ (m n p : ℕ) → m ≤ n → p * m ≤ p * n
*-monoʳ-≤ .0 n p z≤n rewrite *-zeroʳ p = z≤n
*-monoʳ-≤ (suc m) (suc n) p (s≤s m≤n)
  rewrite +-*-suc p m | +-*-suc p n = +-monoʳ-≤ p (*-monoʳ-≤ m n p m≤n)

*-mono-≤ : ∀ (a b c d : ℕ) → a ≤ b → c ≤ d → a * c ≤ b * d
*-mono-≤ a b c d a≤b c≤d = ≤-trans (*-monoˡ-≤ a b c a≤b) (*-monoʳ-≤ c d b c≤d)

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ {a b c : ℕ} → a < b → b < c → a < c
<-trans z<s (s<s b<c) = z<s
<-trans (s<s a<b) (s<s b<c) = s<s (<-trans a<b b<c)

data Trichotomy : ℕ → ℕ → Set where
  a<b : ∀ {a b : ℕ} → a < b → Trichotomy a b
  a≡b : ∀ {a b : ℕ} → a ≡ b → Trichotomy a b
  a>b : ∀ {a b : ℕ} → b < a → Trichotomy a b

<-trichotomous : ∀ (a b : ℕ) → Trichotomy a b
<-trichotomous zero zero = a≡b refl
<-trichotomous zero (suc b) = a<b z<s
<-trichotomous (suc a) zero = a>b z<s
<-trichotomous (suc a) (suc b) with <-trichotomous a b
... | a<b m<n = a<b (s<s m<n)
... | a≡b m≡n = a≡b (cong suc m≡n)
... | a>b n<m = a>b (s<s n<m)

<-+-suc : ∀ (m n : ℕ) → n < suc m + n
<-+-suc m zero = z<s
<-+-suc m (suc n) rewrite +-suc m n = s<s (<-+-suc m n)

+-monoˡ-< : ∀ {m n : ℕ} → ∀ (p : ℕ) → m < n → m + p < n + p
+-monoˡ-< {m} {suc n} p z<s = <-+-suc n p
+-monoˡ-< p (s<s m<n) = s<s (+-monoˡ-< p m<n)

+-monoʳ-< : ∀ {m n : ℕ} → ∀ (p : ℕ) → m < n → p + m < p + n
+-monoʳ-< zero m<n = m<n
+-monoʳ-< (suc p) m<n = s<s (+-monoʳ-< p m<n)

+-mono-< : ∀ {m n p q : ℕ} → m < n → p < q → m + p < n + q
+-mono-< {m} {n} {p} {q} m<n p<q =
  <-trans (+-monoˡ-< p m<n) (+-monoʳ-< n p<q)

≤-<-suc : ∀ {m n : ℕ} → m ≤ n → m < suc n
≤-<-suc z≤n = z<s
≤-<-suc (s≤s m≤n) = s<s (≤-<-suc m≤n)

suc-≤-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
suc-≤-< (s≤s sm≤n) = ≤-<-suc sm≤n

<-suc-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-suc-≤ z<s = s≤s z≤n
<-suc-≤ (s<s m<n) = s≤s (<-suc-≤ m<n)

suc-< : ∀ {m n} → suc m < n → m < n
suc-< {zero} (s<s sm<n) = z<s
suc-< {suc m} (s<s sm<n) = s<s (suc-< sm<n)

<-trans-revisited : ∀ {m n o : ℕ} → m < n → n < o → m < o
<-trans-revisited m<n n<o =
  suc-< (suc-≤-< (≤-trans (<-suc-≤ (s<s m<n)) (<-suc-≤ n<o)))

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even 0
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)

e+o≡o zero on = on
e+o≡o (suc x) on = suc (o+o≡e x on)

o+o≡e (suc em) on = suc (e+o≡o em on)

data One : Bin → Set where
  one-⟨⟩ : One (⟨⟩ I)
  one-I : ∀ {b : Bin} → One b → One (b I)
  one-O : ∀ {b : Bin} → One b → One (b O)

data Can : Bin → Set where
  can-⟨⟩ : Can ⟨⟩
  can-one : ∀ {b : Bin} → One b → Can b

inc-one : ∀ {b : Bin} → One b → One (inc b)
inc-one one-⟨⟩ = one-O one-⟨⟩
inc-one (one-I ob) = one-O (inc-one ob)
inc-one (one-O ob) = one-I ob

inc-can : ∀ {b : Bin} → Can b → Can (inc b)
inc-can can-⟨⟩ = can-one one-⟨⟩
inc-can (can-one ob) = can-one (inc-one ob)

to-can : ∀ (n : ℕ) → Can (to n)
to-can zero = can-⟨⟩
to-can (suc n) = inc-can (to-can n)

<-suc : ∀ {m n : ℕ} → m < n → m < suc n
<-suc z<s = z<s
<-suc (s<s m<n) = s<s (<-suc m<n)

<-+-right : ∀ {m n : ℕ} → (o : ℕ) → m < n → m < n + o
<-+-right o z<s = z<s
<-+-right o (s<s m<n) = s<s (<-+-right o m<n)

one>0 : ∀ {b : Bin} → One b → 0 < from b
one>0 one-⟨⟩ = z<s
one>0 (one-I ob) = z<s
one>0 {b O} (one-O ob) = <-+-right (from b + zero) (one>0 ob)

double-app-zero : ∀ (n : ℕ) → 0 < n → to (n + n) ≡ (to n O)
double-app-zero zero ()
double-app-zero (suc zero) n>0 = refl
double-app-zero (suc (suc n)) n>0
  rewrite +-suc n (suc n)
        | double-app-zero (suc n) z<s = refl

to-from-one : ∀ {b : Bin} → One b → to (from b) ≡ b
to-from-one one-⟨⟩ = refl
to-from-one {b I} (one-I ob)
  rewrite +-identityʳ (from b)
        | double-app-zero (from b) (one>0 ob)
        | to-from-one ob = refl
to-from-one {b O} (one-O ob)
  rewrite +-identityʳ (from b)
        | double-app-zero (from b) (one>0 ob)
        | to-from-one ob = refl

to-from : ∀ {b : Bin} → Can b → to (from b) ≡ b
to-from can-⟨⟩ = refl
to-from (can-one ob) = to-from-one ob
