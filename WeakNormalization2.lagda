\begin{code}
module WeakNormalization2 where

open import Atom
open import ListProperties
open import Chi
open import NaturalProperties
open import Term hiding (fv)
open import Relation hiding (_⊆_;_++_)
open import Beta
open import Substitution
open import TermInduction
open import Permutation
open import FreeVariables
open import Alpha renaming (τ to ∼τ)
open import Types

open import Data.Bool hiding (_∨_;_≟_)
open import Data.Product renaming (Σ to Σₓ;map to mapₓ;_,_ to _∶_) public
open import Data.Sum renaming (_⊎_ to _∨_;map to map+)
open import Data.Empty
open import Function
open import Relation.Nullary 
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_]) renaming (trans to trans≡)
open import Data.List
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡  renaming (_∈_ to _∈l_;_⊆_ to _⊆l_;_∉_ to _∉l_)
open import Data.List.Any.Properties
open import Data.Nat as Nat hiding (_⊔_;_*_)
open import Data.Nat.Properties
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)
\end{code}


Weak Normalization

\begin{code}
data Ne : V → Λ → Set
data Nf : Λ → Set

data Ne where
  v   : (x : V) → Ne x (v x)
  _·_ : ∀ {x r s} → Ne x r → Nf s → Ne x (r · s) 

data Nf where
  ne  : ∀ {x r} → Ne x r → Nf r
  ƛ : ∀ {x r} → Nf r → Nf (ƛ x r)

infix 4 _↓
infix 5 _↓_

_↓_ : Λ → Λ → Set
M ↓ N = M →α* N × Nf N 

_↓ : Λ → Set
M ↓ = ∃ (λ N → M ↓ N)
\end{code}


\begin{code}
lemma₁ : {x : Atom}{Γ : Cxt}{α β : Type}{M N : Λ}
  → Γ ‚ x ∶ β ⊢ M ∶ α
  → Γ ⊢ N ∶ β
  → Nf N
  → M [ x ≔ N ] ↓
lemma₂ : {x : Atom}{Γ : Cxt}{α β γ : Type}{M N P Q : Λ}
  → Γ ‚ x ∶ β ⊢ M ∶ γ ⟶ α
  → Γ ⊢ N ∶ β
  → Γ ⊢ Q ∶ γ  
  → Nf N → Nf Q
  → M [ x ≔ N ] ↓ P
  → P · Q ↓

lemma₁ {x} {M = v y}   {N}  _                           _ nfN with (v y) [ x ≔ N ] | lemmahvar {x} {y} {N}
... | .N     | inj₁ (x≡y ∶ refl) = N   ∶ refl ∶ nfN
... | .(v y) | inj₂ (x≢y ∶ refl) = v y ∶ refl ∶ ne (v y)
lemma₁ {x} {Γ} .{α} {β} {M · P} {N}  (⊢· {γ} {α} Γ,x:β⊢M:γ→α Γ,x:β⊢P:γ)  Γ⊢N:β nfN
  with lemma₁ Γ,x:β⊢M:γ→α Γ⊢N:β nfN | lemma₁ Γ,x:β⊢P:γ Γ⊢N:β nfN -- llamdas achican M pero crece en tipo
... | Q ∶ M[x≔N]→Q ∶ nfQ | R ∶ P[x≔N]→R ∶ nfR 
  with lemma₂ {x} {Γ} {α} {β} {γ} Γ,x:β⊢M:γ→α Γ⊢N:β {!!} nfN nfR (M[x≔N]→Q ∶ nfQ) -- llamada se achica en M pero crece en tipo
... | S ∶ QR→S ∶ nfS =  S ∶ trans (app-star M[x≔N]→Q P[x≔N]→R) QR→S ∶ nfS
lemma₁ {x} {M = ƛ y M} {N}  (⊢ƛ Γ,x:β,y:α⊢M:α→γ)        Γ⊢N:β nfN
  with χ (x ∷ fv N) (ƛ y M) | χ# (x ∷ fv N) (ƛ y M) | χ∉ (x ∷ fv N) (ƛ y M) | (ƛ y M) [ x ≔ N ] | lemmaSubstƛ x y M N | lemma∼λχ {y} {x ∷ fv N} {M}
... | z | z#λyM | z∉x∷fvN | .(ƛ z ((（ y ∙ z ） M ) [ x ≔ N ])) | refl | λyM∼λz（yz）M = {!!}


lemma₂ {x} {M = v y} {N} {P}     {Q} _           _    _ nfN nfQ (_          ∶ ne neP) =
  P · Q ∶ refl ∶ ne (neP · nfQ)
lemma₂ {x} {M = v y} {N} {ƛ z P} {Q} Γ,x:β⊢y:α→γ Γ⊢N:β Γ⊢Q∶α nfN nfQ (y[x≔N]→ƛzP ∶  ƛ nfP)
  with lemma⊢→α* (lemma⊢[] Γ,x:β⊢y:α→γ Γ⊢N:β) y[x≔N]→ƛzP  
... | ⊢ƛ Γ,z:α⊢P:γ = ? -- with lemma₁ Γ,z:α⊢P:γ Γ⊢Q∶α nfQ -- solo achica el tipo, pero el termino es p
-- ... | R ∶ P[z≔Q]→R ∶ nfR = R ∶ trans (just (inj₁ (ctxinj ▹β))) P[z≔Q]→R ∶ nfR  
lemma₂ {M = M · N} = {!!}
lemma₂ {M = ƛ y N} = {!!}
\end{code}


