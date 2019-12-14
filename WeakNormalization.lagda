\begin{code}
module WeakNormalization where

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

ƛ↓ : {x : Atom}{M : Λ} → M ↓ → ƛ x M ↓
ƛ↓ {x} {M} (N ∶ M→N ∶ nfN) = ƛ x N ∶ abs-star M→N ∶ ƛ nfN
\end{code}

\begin{code}
lemma₂var : {x  y : Atom}{N : Λ} → Nf N → (v y) [ x ≔ N ] ↓
lemma₂var = {!!}

lemma₁ : {α β : Type}{Γ : Cxt}{M N : Λ} → Nf M → Nf N → Γ ⊢ M ∶ α ⟶ β → Γ ⊢ N ∶ α → M · N ↓ 
lemma₂ : {α β : Type}{Γ : Cxt}{x : Atom}{M N : Λ} → Nf M → Nf N → Γ ‚ x ∶ β  ⊢ M ∶ α  →  Γ ⊢ N ∶ β → M [ x ≔ N ] ↓
-- lemma₃ : {x y : Atom}{Γ : Ctx}{α β : Type}{M : Λ} → Ne x M → Γ ‚ x ∶ β ⊢ M ∶ α → Γ ⊢ v y ∶ β  → ∃ (λ z → λ M → Ne z M × M [ x ≔ ] →α* r')
-- lemma₄ : ∀ {x Γ Δ α β σ} → Acc< β → (r : Λ) → Ne x r → Γ ⊢ r ∶ α → Π σ r β Γ Δ → ¬ isVar (σ x) → r ∙ σ ↓ ∧ α ≤ β 

lemma₁ {M = v x}    {N} _          nfN _               _  = (v x)   · N ∶ refl ∶ ne (v x · nfN)  
lemma₁ {M = M · P}  {N} (ne neMP)  nfN _               _  = (M · P) · N ∶ refl ∶ ne (neMP · nfN) 
lemma₁ {M = ƛ x M}  {N} (ne ())    nfN _               _
lemma₁ {M = ƛ x M}  {N} (ƛ nfM)    nfN (⊢ƛ Γ,x:β⊢M:α)  Γ⊢N:β
  with lemma₂ nfM nfN Γ,x:β⊢M:α Γ⊢N:β
... | P ∶ M[x≔N]→P ∶ nfP = P ∶ trans (just (inj₁ (ctxinj ▹β))) M[x≔N]→P  ∶ nfP

lemma₂ {x = x} {v y}   {N} _                nfN _                          _      = lemma₂var {x} nfN
lemma₂ {x = x} {M · P} {N} (ne (neM · nfP)) nfN (⊢· Γ,x:β⊢M:α→γ Γ,x:β⊢P:α) Γ⊢N:β
  with lemma₂ (ne neM) nfN Γ,x:β⊢M:α→γ Γ⊢N:β | lemma₂ nfP nfN Γ,x:β⊢P:α Γ⊢N:β
... | Q ∶ M[x≔N]→Q ∶ nfQ | R ∶ P[x≔N]→R ∶ nfR
  with lemma₁ nfQ nfR (lemma⊢→α* (lemma⊢[] Γ,x:β⊢M:α→γ Γ⊢N:β) M[x≔N]→Q) (lemma⊢→α* (lemma⊢[] Γ,x:β⊢P:α Γ⊢N:β) P[x≔N]→R)
... | S ∶ QR→S ∶ nfS = S ∶ trans (app-star M[x≔N]→Q P[x≔N]→R) QR→S ∶ nfS
lemma₂ {x = x} {ƛ y M} {N} = {!!}

wk : {α : Type}{Γ : Cxt}{M : Λ} → Γ ⊢ M ∶ α → M ↓
wk {M = v x}   _                  = v x ∶ refl ∶ ne (v x)
wk {M = ƛ x M} (⊢ƛ Γ,x:β⊢M:α)     = ƛ↓ (wk Γ,x:β⊢M:α)
wk {M = M · N} (⊢· Γ⊢M:α→β Γ⊢N:α)
  with wk Γ⊢M:α→β | wk Γ⊢N:α
... | M' ∶ M→M' ∶ nfM' | N' ∶ N→N' ∶ nfN'
  with lemma₁ nfM' nfN' (lemma⊢→α* Γ⊢M:α→β M→M') (lemma⊢→α* Γ⊢N:α N→N')
... | P ∶ M'N'→P ∶ nfP = P ∶ trans (app-star M→M' N→N') M'N'→P ∶ nfP  
\end{code}


