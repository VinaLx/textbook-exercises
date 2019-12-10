module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Nat.Properties

open import plfa.part1.Naturals

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    m + n + p
  ≡⟨ cong (λ x → x + p) (+-comm m n) ⟩
    n + m + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

*-distrib-+′ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+′ zero n p = refl
*-distrib-+′ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (λ x → p + x) (*-distrib-+′ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    p + m * p + n * p
  ∎

*-distrib-+″ : ∀ (m n p : ℕ) → m * (n + p) ≡ m * n + m * p
*-distrib-+″ zero n p = refl
*-distrib-+″ (suc m) n p =
  begin
    (n + p) + m * (n + p)
  ≡⟨ cong (λ x → n + p + x) (*-distrib-+″ m n p)  ⟩
    n + p + (m * n + m * p)
  ≡⟨ +-assoc n p (m * n + m * p) ⟩
    n + (p + (m * n + m * p))
  ≡⟨ cong (λ x → n + x) (sym (+-assoc p (m * n) (m * p))) ⟩
    n + (p + m * n + m * p)
  ≡⟨ cong (λ x → n + (x + m * p)) (+-comm p (m * n)) ⟩
    n + (m * n + p + m * p)
  ≡⟨ cong (λ x → n + x) (+-assoc (m * n) p (m * p)) ⟩
    n + (m * n + (p + m * p))
  ≡⟨ sym (+-assoc n (m * n) (p + m * p)) ⟩
    n + m * n + (p + m * p)
  ∎

*-assoc′ : ∀ (m n p : ℕ) → m * n * p ≡ m * (n * p)
*-assoc′ zero n p = refl
*-assoc′ (suc m) n p =
  begin
    (suc m) * n * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distrib-+′ n (m * n) p ⟩
    n * p + m * n * p
  ≡⟨ cong ((_+_) (n * p)) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ∎

*-comm′ : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm′ zero n =
  begin
    0 * n
  ≡⟨ sym (*-zeroʳ n) ⟩
    n * 0
  ∎
*-comm′ (suc m) n =
  begin
    n + m * n
  ≡⟨ cong (λ x → n + x) (*-comm′ m n) ⟩
    n + n * m
  ≡⟨ cong (λ x → x + n * m) (sym (*-identityʳ n)) ⟩
    n * 1 + n * m
  ≡⟨ sym (*-distrib-+″ n 1 m) ⟩
    n * (1 + m)
  ∎

∸-0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-0 zero = refl
∸-0 (suc n) = refl

∸-+-assoc′ : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc′ zero n p =
  begin
    0 ∸ n ∸ p
  ≡⟨ cong (λ x → x ∸ p) (∸-0 n) ⟩
    0 ∸ p
  ≡⟨ ∸-0 p ⟩
    0
  ≡⟨ sym (∸-0 (n + p)) ⟩
    0 ∸ (n + p)
  ∎
∸-+-assoc′ (suc m) n p with n
... | zero = refl
... | suc n₁ = ∸-+-assoc′ m n₁ p

^-distribute-*-+ : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribute-*-+ m zero p =
  begin
    m ^ p
  ≡⟨ sym (*-identityˡ (m ^ p)) ⟩
    1 * m ^ p
  ∎
^-distribute-*-+ m (suc n) p =
  begin
    m * m ^ (n + p)
  ≡⟨ cong (_*_ m) (^-distribute-*-+ m n p) ⟩
    m * (m ^ n * m ^ p)
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m * m ^ n * m ^ p
  ∎

^-distribute-*-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ m ^ p * n ^ p
^-distribute-*-* m n zero = refl
ke^-distribute-*-* m n (suc p) =
  begin
    m * n * (m * n) ^ p
  ≡⟨ cong (_*_ (m * n)) (^-distribute-*-* m n p) ⟩
    m * n * (m ^ p * n ^ p)
  ≡⟨ *-assoc m n ((m ^ p) * (n ^ p)) ⟩
    m * (n * (m ^ p * n ^ p))
  ≡⟨ sym (cong (_*_ m) (*-assoc n (m ^ p) (n ^ p))) ⟩
    m * (n * m ^ p * n ^ p)
  ≡⟨ sym (cong (λ z → m * (z * (n ^ p))) (*-comm (m ^ p) n)) ⟩
    m * (m ^ p * n * n ^ p)
  ≡⟨ cong (_*_ m) (*-assoc (m ^ p) n (n ^ p)) ⟩
    m * (m ^ p * (n * n ^ p))
  ≡⟨ sym (*-assoc m (m ^ p) (n * (n ^ p))) ⟩
    m * m ^ p * (n * n ^ p)
  ∎

^-distribute-*-^ : ∀ (m n p : ℕ) → m ^ (n * p) ≡ (m ^ n) ^ p
^-distribute-*-^ m zero p rewrite ^-zeroˡ p = refl
^-distribute-*-^ m (suc n) p =
  begin
    m ^ (p + n * p)
  ≡⟨ ^-distribute-*-+ m p (n * p) ⟩
    m ^ p * m ^ (n * p)
  ≡⟨ cong (_*_ (m ^ p)) (^-distribute-*-^ m n p) ⟩
    m ^ p * (m ^ n) ^ p
  ≡⟨ sym (^-distribute-*-* m (m ^ n) p) ⟩
    (m * m ^ n) ^ p
  ∎
