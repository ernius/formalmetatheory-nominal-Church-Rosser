\begin{code}
module ListProperties where

open import Function
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_;map to map+)
open import Data.Nat
open import Data.Product renaming (Σ to Σₓ;map to mapₓ) 
open import Data.Bool hiding (_∨_;_≟_)
open import Data.List hiding (any)
open import Data.List hiding (any)
open import Data.List.Properties
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Properties
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 

open Any.Membership-≡ renaming (_∈_ to _∈'_;_∉_ to _∉'_) 
import Function.Equality as FE
open import Function.Inverse hiding (sym;_∘_;map;id)
open Inverse

-- Auxiliary Lemmas about lists membership
c∈xs++ys→c∈xs∨c∈ys : {x : ℕ}{xs ys : List ℕ} → x ∈' xs ++ ys → (x ∈' xs) ∨ (x ∈' ys) 
c∈xs++ys→c∈xs∨c∈ys {x} {xs} {ys} = FE.Π._⟨$⟩_ (from (++↔ {A = ℕ} {P = _≡_ x} {xs = xs} {ys = ys})) 
c∈xs∨c∈ys→c∈xs++ys : {x : ℕ}{xs ys : List ℕ} → x ∈' xs ∨ x ∈' ys → x ∈' xs ++ ys 
c∈xs∨c∈ys→c∈xs++ys {x} {xs} {ys} = FE.Π._⟨$⟩_ (to (++↔ {A = ℕ} {P = _≡_ x} {xs = xs} {ys = ys})) 
c∉xs++ys→c∉xs : {c : ℕ}{xs ys : List ℕ} → c ∉' xs ++ ys → c ∉' xs 
c∉xs++ys→c∉xs {c} {xs} {ys} c∉xs++ys c∈xs = c∉xs++ys (c∈xs∨c∈ys→c∈xs++ys (inj₁ c∈xs))
c∉xs++ys→c∉ys : {c : ℕ}{xs ys : List ℕ} → c ∉' xs ++ ys → c ∉' ys 
c∉xs++ys→c∉ys {c} {xs} {ys} c∉xs++ys c∈ys = c∉xs++ys (c∈xs∨c∈ys→c∈xs++ys {c} {xs} {ys} (inj₂ c∈ys))
d∉abc∷xs→d≢a : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ≢ a
d∉abc∷xs→d≢a {a} {b} {c} {.a} {xs} d∉abc∷xs refl = ⊥-elim (d∉abc∷xs (here refl))
d∉abc∷xs→d≢b : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ≢ b
d∉abc∷xs→d≢b {a} {b} {c} {.b} {xs} d∉abc∷xs refl = ⊥-elim (d∉abc∷xs (there (here refl)))
d∉abc∷xs→d≢c : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ≢ c
d∉abc∷xs→d≢c {a} {b} {c} {.c} {xs} d∉abc∷xs refl = ⊥-elim (d∉abc∷xs (there (there (here refl))))
d∉abc∷xs→d∉xs : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ∉' xs
d∉abc∷xs→d∉xs {a} {b} {c} {d} {xs} d∉abc∷xs d∈xs = ⊥-elim (d∉abc∷xs (there (there (there d∈xs))))
d∉ab∷xs→d∉xs : {a b  d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ xs) → d ∉' xs
d∉ab∷xs→d∉xs {a} {b} {d} {xs} d∉ab∷xs d∈xs = ⊥-elim (d∉ab∷xs (there (there d∈xs)))
b∉a∷xs→b≢a : {a b : ℕ}{xs : List ℕ} → b ∉' (a ∷ xs) → b ≢ a
b∉a∷xs→b≢a {a} {.a} {xs} a∉a∷xs refl = ⊥-elim (a∉a∷xs (here refl))
b∉a∷xs→b∉xs : {a b : ℕ}{xs : List ℕ} → b ∉' (a ∷ xs) → b ∉' xs 
b∉a∷xs→b∉xs {a} {b} {xs} b∉a∷xs b∈xs = ⊥-elim (b∉a∷xs (there b∈xs))
c∉x∷xs++ys→c∉x∷xs : {a b : ℕ}{xs ys : List ℕ} → a ∉' (b ∷ (xs ++ ys)) → a ∉' b ∷ xs 
c∉x∷xs++ys→c∉x∷xs a∉b∷xs++ys (here a≡b)    = ⊥-elim (a∉b∷xs++ys (here a≡b))
c∉x∷xs++ys→c∉x∷xs a∉b∷xs++ys (there a∈xs)  = ⊥-elim ((c∉xs++ys→c∉xs (b∉a∷xs→b∉xs a∉b∷xs++ys)) a∈xs)
c∉x∷xs++ys→c∉x∷ys : {a b : ℕ}{xs ys : List ℕ} → a ∉' (b ∷ (xs ++ ys)) → a ∉' b ∷ ys 
c∉x∷xs++ys→c∉x∷ys a∉b∷xs++ys (here a≡b)              = ⊥-elim (a∉b∷xs++ys (here a≡b))
c∉x∷xs++ys→c∉x∷ys {xs = xs} a∉b∷xs++ys (there a∈ys)  = ⊥-elim ((c∉xs++ys→c∉ys {xs = xs} (b∉a∷xs→b∉xs a∉b∷xs++ys)) a∈ys)
x≢y∧y∉xs→x∉x∷xs : {x y : ℕ}{xs : List ℕ} → x ≢ y → y ∉' xs → y ∉' x ∷ xs
x≢y∧y∉xs→x∉x∷xs {x} .{x} x≢x _ (here refl) =  ⊥-elim (x≢x refl)
x≢y∧y∉xs→x∉x∷xs {x} {y} x≢y y∉xs (there y∈xs) = ⊥-elim (y∉xs y∈xs)
--
lemmaxs++[]≡xs : {A : Set}(xs : List A) → xs ++ [] ≡ xs
lemmaxs++[]≡xs []        =  refl
lemmaxs++[]≡xs (x ∷ xs)  =  cong (_∷_ x) (lemmaxs++[]≡xs xs)
-- Auxiliary functions and properties
_-_ : List ℕ → ℕ → List ℕ
xs - x = filter (λ y → not (⌊ x ≟ y ⌋)) xs
--
-prop : ∀ {a b} → b ≢ a → not ⌊ b ≟ a ⌋ ≡ true
-prop {a} {b} b≢a with b ≟ a 
... | yes b≡a  = ⊥-elim (b≢a b≡a)
... | no _     = refl
--
lemmafilter→ : (x : ℕ)(xs : List ℕ)(p : ℕ → Bool) → x ∈' filter p xs → (p x ≡ true × x ∈' xs)
lemmafilter→ x []        p ()
lemmafilter→ x (y ∷ xs)  p x∈filterpy∷xs with p y | inspect p y
...  | false   | [ py≡false ]ᵢ = mapₓ id there (lemmafilter→ x xs p x∈filterpy∷xs)
lemmafilter→ x (.x ∷ xs) p (here refl)         
     | true | [ px≡true ]ᵢ = px≡true , here refl
lemmafilter→ x (y ∷ xs) p (there x∈filterpxs)  
     | true | [ py≡true ]ᵢ = mapₓ id there (lemmafilter→ x xs p x∈filterpxs)
--
lemmafilter← : (x : ℕ)(xs : List ℕ)(p : ℕ → Bool) → p x ≡ true →  x ∈' xs → x ∈' filter p xs
lemmafilter← x (.x ∷ xs)  p px≡true (here refl) with p x
lemmafilter← x (.x ∷ xs)  p px≡true (here refl) | true = here refl
lemmafilter← x (.x ∷ xs)  p ()      (here refl) | false 
lemmafilter← x (y ∷ xs)   p px≡true (there x∈xs) with p y
... | false = lemmafilter← x xs p px≡true x∈xs
... | true  = there (lemmafilter← x xs p px≡true x∈xs)
--
lemmaΓ⊆Δ→Γ,x⊆Δ,x : {x : ℕ}{Γ Δ : List ℕ} → Γ ⊆ Δ → x ∷ Γ ⊆ x ∷ Δ
lemmaΓ⊆Δ→Γ,x⊆Δ,x {x} Γ⊆Δ {y} (here y≡x)     = here y≡x
lemmaΓ⊆Δ→Γ,x⊆Δ,x {x} Γ⊆Δ {y} (there y∈Γ,x)  = there (Γ⊆Δ y∈Γ,x)
--
lemmaΓ⊆Γ,x : {Γ : List ℕ}{x : ℕ} → Γ ⊆ x ∷ Γ
lemmaΓ⊆Γ,x {Γ} {x} {y} y∈Γ = there y∈Γ
--
lemmax∈Γ⇒Γ,x⊆Γ : {Γ : List ℕ}{x : ℕ} → x ∈' Γ → x ∷ Γ ⊆ Γ
lemmax∈Γ⇒Γ,x⊆Γ x∈Γ (here refl)  = x∈Γ
lemmax∈Γ⇒Γ,x⊆Γ x∈Γ (there y∈Γ)  = y∈Γ
--
lemma∈ : {Γ : List ℕ}{x y : ℕ} → y ∈' x ∷ Γ → x ≢ y → y ∈' Γ
lemma∈ {Γ} {x} .{x}  (here refl) x≢y = ⊥-elim (x≢y refl)
lemma∈ {Γ} {x} {y}   (there y∈Γ) x≢y = y∈Γ
--
lemmaΓ⊆Γ++Γ : {Γ : List ℕ} → Γ ++ Γ ⊆ Γ
lemmaΓ⊆Γ++Γ x∈Γ++Γ with c∈xs++ys→c∈xs∨c∈ys x∈Γ++Γ 
... | inj₁ x∈Γ = x∈Γ
... | inj₂ x∈Γ = x∈Γ
--
lemmaΓ⊆Γ++Δ : {Γ Δ : List ℕ} → Γ ⊆ Γ ++ Δ
lemmaΓ⊆Γ++Δ x∈Γ = c∈xs∨c∈ys→c∈xs++ys (inj₁ x∈Γ)
--
lemmaΓ,x,y⊆Γ,y,x : {x y : ℕ}{Γ : List ℕ} → y ∷ x ∷ Γ ⊆ x ∷ y ∷ Γ
lemmaΓ,x,y⊆Γ,y,x (here refl)          = there (here refl)
lemmaΓ,x,y⊆Γ,y,x (there (here refl))  = here refl
lemmaΓ,x,y⊆Γ,y,x (there (there z∈Γ))  = there (there z∈Γ)
--
lemmaΓ++Δ,x⊆Γ,x++Δ : {Γ Δ : List ℕ}{x : ℕ} → Γ ++ x ∷ Δ ⊆ x ∷ Γ ++ Δ
lemmaΓ++Δ,x⊆Γ,x++Δ {Γ} {Δ} {x} {y} y∈Γ++x∷Δ with c∈xs++ys→c∈xs∨c∈ys {y} {Γ} {x ∷ Δ} y∈Γ++x∷Δ
... | inj₁ y∈Γ          = c∈xs∨c∈ys→c∈xs++ys (inj₁ (there y∈Γ))
... | inj₂ (here y≡x)   = here y≡x
... | inj₂ (there y∈Δ)  = c∈xs∨c∈ys→c∈xs++ys {y} {x ∷ Γ} (inj₂ y∈Δ)
\end{code}

First element to satisfy some property.

\begin{code}
data First {A : Set}
         (P : A → Set) : List A → Set where
  here  : ∀ {x xs} (px  : P x)                        → First P (x ∷ xs)
  there : ∀ {x xs} (¬px : ¬ (P x))(pxs : First P xs)  → First P (x ∷ xs)
\end{code}


