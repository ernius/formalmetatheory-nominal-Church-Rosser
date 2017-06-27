\begin{code}
module Chi where

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Bool hiding (_≟_;_∨_)
open import Data.Empty
open import Function
open import Data.Sum hiding (map) renaming (_⊎_ to _∨_)
open import Data.Product renaming (Σ to Σₓ;map to mapₓ) 
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 
open import Data.List hiding (any) renaming (length to length') 
open import Data.List.Properties
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open import Data.List.Any.Properties
open Any.Membership-≡ renaming (_∈_ to _∈[]_;_∉_ to _∉[]_) 
open import Algebra.Structures
open import Relation.Binary
--
n+0≡n   = IsCommutativeMonoid.identityˡ (IsCommutativeSemiring.*-isCommutativeMonoid isCommutativeSemiring)
+-comm  = IsCommutativeMonoid.comm (IsCommutativeSemiring.+-isCommutativeMonoid isCommutativeSemiring)
total   = IsTotalOrder.total (IsDecTotalOrder.isTotalOrder (DecTotalOrder.isDecTotalOrder decTotalOrder))
--
V = ℕ
--
f<s : (x : V)(xs : List V) → x ∈[] xs → ((y : V) → y < x → y ∈[] xs) → (y : V) → y < (suc x) → y ∈[] xs
f<s x xs x∈xs f< y sucy≤sucx with ≤⇒≤′ sucy≤sucx
f<s x xs x∈xs f< .x _ | ≤′-refl            = x∈xs
f<s x xs x∈xs f< y  _ | ≤′-step sucy<'sucx = f< y (≤′⇒≤ sucy<'sucx)
--
χaux : (n m k : V) → n + m ≡ k → (xs : List V) → ((y : V) → y < n → y ∈[] xs) → 
       ∃ (λ v → (v ∉[] xs ∨ v ≡ k) × ((y : V) → y < v → y ∈[] xs))
χaux x 0        k   x+0≡k   _  f<  with trans (sym (n+0≡n x)) x+0≡k
χaux x 0        .x  x+0≡k   _  f<  | refl
  = x , inj₂ refl , f<
χaux x (suc n)  k   x+Sn≡k  xs f<
  with any (_≟_ x) xs
... | no  x∉xs = x , inj₁ x∉xs , f<
... | yes x∈xs = χaux (suc x) n k (trans (cong suc (+-comm x n)) (trans (+-comm (suc n) x) x+Sn≡k)) xs (f<s x xs x∈xs f<) 
--
y<0⇒y∈xs : (xs : List V)(y : V) → y < 0 → y ∈[] xs
y<0⇒y∈xs xs y () 
\end{code}

%<*chiaux>
\begin{code}
χ' : List V → V
\end{code}
%</chiaux>

\begin{code}
χ' xs = proj₁ (χaux 0 (length' xs) (length' xs) refl xs (y<0⇒y∈xs xs))
--
sucn≡sucm→n≡m : {n m : ℕ} → suc n ≡ suc m → n ≡ m
sucn≡sucm→n≡m refl = refl
--
predn≡m→n≡sucm : {n m : ℕ} → n > 0 → pred n ≡ m → n ≡ suc m
predn≡m→n≡sucm {suc n} {m} (s≤s _) n≡m = cong suc n≡m
--
x∈xs→|xs|>0 : {n : ℕ}{x : ℕ}{xs : List ℕ} → x ∈[] xs → n ≡ length' xs → n > 0
x∈xs→|xs|>0 .{suc (length' xs)} {x} {y ∷ xs} (here px)     refl = s≤s z≤n
x∈xs→|xs|>0 .{suc (length' xs)} {x} {y ∷ xs} (there x∈xs)  refl = s≤s z≤n
--
del : (n : ℕ)(x : ℕ)(xs : List ℕ) → n ≡ length' xs → x ∈[] xs → Σₓ (List ℕ) (λ ys → pred n ≡ length' ys)
del .0       x   []        refl       ()
del 0        _   (x ∷ xs)  ()         _
del (suc n)  .x  (x ∷ xs)  n+1≡|xxs|  (here refl)
  =  xs , sucn≡sucm→n≡m n+1≡|xxs|
del (suc n)  x   (y ∷ xs)  n+1≡|yxs|  (there x∈xs)  
  =  y ∷ proj₁ (del n x xs n≡|xs| x∈xs) ,  
     predn≡m→n≡sucm (x∈xs→|xs|>0 x∈xs n≡|xs|) (proj₂ (del n x xs n≡|xs| x∈xs))
    where n≡|xs| = sucn≡sucm→n≡m n+1≡|yxs|
--
<→≢ : {n m : ℕ} → n < m → n ≢ m
<→≢ (s≤s n<m) refl = ⊥-elim (aux n<m)
  where
  aux : {n : ℕ} → suc n ≤ n → ⊥
  aux (s≤s sucn≤n) = aux sucn≤n
--
del∈ : (x : ℕ)(xs : List ℕ) → (x∈xs : x ∈[] xs) → (y : ℕ) → y < x → y ∈[] xs → y ∈[] (proj₁ (del (length' xs) x xs refl x∈xs))
del∈ x []         ()            y   y<x y∈xs 
del∈ x (.x ∷ xs)  (here refl)   .x  x<x (here refl)    = ⊥-elim ((<→≢ x<x) refl)
del∈ x (.x ∷ xs)  (here refl)   y   y<x (there y∈xs)   = y∈xs
del∈ x (.y ∷ xs)  (there x∈xs)  y   y<x (here refl)    = here refl
del∈ x (z ∷ xs)   (there x∈xs)  y   y<x (there y∈xs)   = there (del∈ x xs x∈xs y y<x y∈xs)
--
palomar-aux : (n : ℕ)(xs : List V) → ((y : V) → y ≤ n → y ∈[] xs) → n ≡ length' xs → ⊥
palomar-aux .0 []        f refl with f 0 z≤n
... | ()
palomar-aux 0 (x ∷ xs) f ()
palomar-aux (suc n) (x ∷ xs) f sucn≡suc|xs| with any (_≟_ (length' (x ∷ xs))) (x ∷ xs)
palomar-aux (suc n) (x ∷ xs) f sucn≡suc|xs| 
    | no |x∷xs|∉x∷xs = ⊥-elim (|x∷xs|∉x∷xs  (f (suc (length' xs)) (subst₂ _≤_ refl (sym sucn≡suc|xs|) (n≤m+n 0 (suc (length' xs))))))
palomar-aux (suc n) (x ∷ xs) f sucn≡suc|xs| 
    | yes |x∷xs|∈x∷xs 
  with proj₁ (del (length' (x ∷ xs)) (length' (x ∷ xs)) (x ∷ xs) refl |x∷xs|∈x∷xs) | 
       proj₂ (del (length' (x ∷ xs)) (length' (x ∷ xs)) (x ∷ xs) refl |x∷xs|∈x∷xs) |
       del∈ (length' (x ∷ xs)) (x ∷ xs) |x∷xs|∈x∷xs 
palomar-aux (suc n) (x ∷ xs)  f sucn≡suc|xs|
    | yes |x∷xs|∈x∷xs | ys | |xs|≡|ys| | f2
 = palomar-aux n ys fys (trans (sucn≡sucm→n≡m sucn≡suc|xs|) |xs|≡|ys|)
  where 
  fys : (y : V) → y ≤ n → y ∈[] ys
  fys y y≤n = f2 y (s≤s (subst₂ _≤_ refl (sucn≡sucm→n≡m sucn≡suc|xs|) y≤n)) (f y (≤-step y≤n))
--
palomar : (n : V)(xs : List V) → ((y : V) → y < n → y ∈[] xs) → n ≡ length' xs → n ∉[] xs
palomar .(length' xs) xs f refl |xs|∈xs = palomar-aux (length' xs) xs (faux (length' xs) xs |xs|∈xs f refl) refl
  where
  faux : (n : ℕ)(xs : List ℕ) → length' xs ∈[] xs → ((y : V) → y < n → y ∈[] xs) → n ≡ length' xs → (y : ℕ)  → y ≤ length' xs → y ∈[] xs
  faux .(length' xs) xs |xs|∈xs  f refl  y y≤|xs| with ≤⇒≤′ y≤|xs| 
  faux .0 [] |xs|∈xs  f refl .0  y≤|xs| 
    | ≤′-refl = |xs|∈xs
  faux .(suc (length' xs)) (x ∷ xs) |xs|∈xs f refl .(suc (length' xs))  y≤|xs|+1 
    | ≤′-refl = |xs|∈xs
  faux .(suc (length' xs)) (x ∷ xs) |xs|∈xs f refl .0      z≤n
    | ≤′-step _ =  f 0 (s≤s z≤n)
  faux .(suc (length' xs)) (x ∷ xs) |xs|∈xs f refl (suc y) (s≤s a)
    | ≤′-step b =  f (suc y) (s≤s (≤′⇒≤ b))
--
lemmaχ∉ : (xs : List V) → χ' xs ∉[] xs 
lemmaχ∉ xs with χaux 0 (length' xs) (length' xs) refl xs (y<0⇒y∈xs xs)
... | v                , inj₁ v∉xs , _   = v∉xs
... | .((length' xs)) , inj₂ refl , f    = palomar (length' xs) xs f refl  
--
≤→<∨≡ : (n m : ℕ) → n ≤ m → n < m ∨ m ≡ n
≤→<∨≡ .0 0 z≤n        =  inj₂ refl
≤→<∨≡ .0 (suc n) z≤n  = inj₁ (s≤s z≤n)
≤→<∨≡ .(suc n) .(suc m) (s≤s {n} {m} n≤m) with ≤→<∨≡ n m n≤m
... | inj₁ n<m        = inj₁ (s≤s n<m)
≤→<∨≡ .(suc n) .(suc n) (s≤s {n} {.n} n≤n) 
    | inj₂ refl       = inj₂ refl  
--
<≡ : (n m : ℕ) → n < m ∨ m < n ∨ n ≡ m
<≡ n m with total n m
... | inj₂ m≤n = inj₂ (≤→<∨≡ m n m≤n)
... | inj₁ n≤m with ≤→<∨≡ n m n≤m
...    | inj₁ n<m = inj₁ n<m
...    | inj₂ n≡m = inj₂ (inj₂ (sym n≡m))
--
lemmaχaux⊆ : (xs ys : List V) → xs ⊆ ys → ys ⊆ xs  → 
    proj₁ (χaux 0 (length' xs) (length' xs) refl xs (y<0⇒y∈xs xs)) ≡ proj₁ (χaux 0 (length' ys) (length' ys) refl ys (y<0⇒y∈xs ys))
lemmaχaux⊆ xs ys xs⊆ys ys⊆xs 
  with
  proj₁ (χaux 0 (length' xs) (length' xs) refl xs (y<0⇒y∈xs xs))  |
  proj₂ (χaux 0 (length' xs) (length' xs) refl xs (y<0⇒y∈xs xs))  |
  lemmaχ∉ xs                                                   |
  proj₁ (χaux 0 (length' ys) (length' ys) refl ys (y<0⇒y∈xs ys))  |
  proj₂ (χaux 0 (length' ys) (length' ys) refl ys (y<0⇒y∈xs ys))  |
  lemmaχ∉ ys
... | x | _ , fx | x∉xs | y | _ , fy | y∉ys 
  with <≡ x y 
... | inj₁ x<y         = ⊥-elim (x∉xs (ys⊆xs (fy x x<y)))
... | inj₂ (inj₁ y<x)  = ⊥-elim (y∉ys (xs⊆ys (fx y y<x)))
... | inj₂ (inj₂ x≡y)  = x≡y
\end{code}




