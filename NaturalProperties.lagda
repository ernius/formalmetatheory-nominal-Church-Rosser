\begin{code}
module NaturalProperties where

open import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
open import Algebra
open import Data.Empty
open import Algebra.Structures
open import Relation.Binary
open import Data.Nat.Properties
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)

+-comm = IsCommutativeMonoid.comm (IsCommutativeSemiring.+-isCommutativeMonoid isCommutativeSemiring)
--
lemmam+sucn≡sucm+n : ∀ {m n} → m + suc n ≡ suc (m + n)
lemmam+sucn≡sucm+n {zero}       = refl
lemmam+sucn≡sucm+n {suc m} {n}  = cong suc (lemmam+sucn≡sucm+n {m} {n})

lemmam+sucn≤sucm+n : ∀ {m n} →  suc (m + n) ≤ m + suc n
lemmam+sucn≤sucm+n {m} {n} rewrite lemmam+sucn≡sucm+n {m} {n} = ≤-refl
--
lemmam≡n→m+1≤n+1 : {m n : ℕ} → n ≡ m → suc m ≤′ suc n
lemmam≡n→m+1≤n+1 {m} {.m} refl = ≤′-refl
--
lemmam>0→n+1≤m+n : {m n : ℕ} → m > zero → suc n ≤′ m + n
lemmam>0→n+1≤m+n {0}     {n} ()
lemmam>0→n+1≤m+n {suc m} {n} 1≤m
  = ≤⇒≤′ (start
            suc n
            ≤⟨ s≤s (n≤m+n m n) ⟩
            suc (m + n)
            ≤⟨ ≤-refl ⟩
            suc m + n
          ◽)
--
lemman>0→m+1≤m+n : {m n : ℕ} → n > zero → suc m ≤′ m + n
lemman>0→m+1≤m+n {m} {n} 1≤n rewrite sym (+-comm n m) = lemmam>0→n+1≤m+n {n} {m} 1≤n  
--
lemmam≡n→m≤n : {m n : ℕ} → m ≡ n → m ≤′ n
lemmam≡n→m≤n {m} {.m} refl = ≤′-refl
--
lemmam>0∧n>0→m+n>1 : ∀ {m n} → m > 0 → n > 0 → m + n > 1
lemmam>0∧n>0→m+n>1 {suc m} {suc n} (s≤s _) (s≤s _) =  start 
                                                        suc (suc zero)
                                                      ≤⟨ s≤s (s≤s (z≤n)) ⟩
                                                        suc (suc (m + n))
                                                      ≤⟨ s≤s (lemmam+sucn≤sucm+n {m} {n}) ⟩                    
                                                        suc (m + suc n)
                                                      ≤⟨ ≤-refl ⟩                    
                                                        suc m + suc n
                                                      ◽
--
>1→¬≤1 : ∀ {n} → n > 1 → n ≤ 1 → ⊥
>1→¬≤1 {n} suc1≤n n≤1 = 1+n≰n {1} (start suc 1 ≤⟨ suc1≤n ⟩ n ≤⟨ n≤1 ⟩ 1 ◽)
--
a≢b∧a≡c→c≢b : {a b c : ℕ} → a ≢ b → a ≡ c → c ≢ b
a≢b∧a≡c→c≢b a≢b refl = a≢b
\end{code}
