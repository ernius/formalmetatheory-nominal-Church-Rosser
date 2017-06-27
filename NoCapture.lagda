\begin{code}
module NoCapture where

open import Atom
open import Alpha
open import ListProperties
open import Term hiding (fv)
open import TermRecursion
open import TermInduction
open import TermAcc
open import NaturalProperties
open import Equivariant
open import Permutation
open import FreeVariables
open import Substitution

open import Data.Bool hiding (_∨_;_≟_)
open import Data.Nat hiding (_*_)
open import Data.Nat.Properties
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.List
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Relation.Binary.PreorderReasoning as PreR
open PreR ≈-preorder
\end{code}

No capture lemma
    
\begin{code}
PC→ : Atom → Atom → Λ → Λ → Set
PC→ a b N M = a ∈ fv (M [ b ≔ N ]) → a ∈ fv M - b ++ fv N
\end{code}

\begin{code}
PC→αComp : ∀ a b N → αCompatiblePred (PC→ a b N)
PC→αComp a b N {M} {P} M∼P PC→M a∈fvP[b≔N] 
  rewrite lemmaSubst1 {P} {M} N b (σ M∼P) | lemma∼αfv {P} {M} (σ M∼P)
  = PC→M a∈fvP[b≔N]  
\end{code}

\begin{code}
lemmaNoCapture : ∀ {a b N M} → PC→ a b N M
lemmaNoCapture {a} {b} {N} {M} 
  = TermαPrimInd (PC→ a b N) (PC→αComp a b N) lemmav lemma· (a ∷ b ∷ fv N , lemmaƛ) M
  where
  lemmav : (c : ℕ) → PC→ a b N (v c)
  lemmav c  a∈fva[b≔N] with (v c) [ b ≔ N ] | lemmahvar {b} {c} {N} 
  lemmav c  a∈fvN
    | .N      | inj₁ (b≡a , refl) 
    = c∈xs∨c∈ys→c∈xs++ys {a} {[ c ] - b} (inj₂ a∈fvN)
  lemmav c (there ()) | .(v c) | inj₂ (b≢c , refl) 
  lemmav .a (here refl) | .(v a) | inj₂ (b≢a , refl) 
    = c∈xs∨c∈ys→c∈xs++ys {a} {[ a ] - b} {fv N} (inj₁ (lemmafilter← a [ a ] (λ y → not (⌊ b ≟ y ⌋)) (-prop b≢a) (here refl)))
  lemma· : (M P : Λ) → PC→ a b N M → PC→ a b N P → PC→ a b N (M · P)
  lemma· M P PC→M PC→P a∈fvMP[b≔N] with c∈xs++ys→c∈xs∨c∈ys {a} {fv (M [ b ≔ N ])} {fv (P [ b ≔ N ])} a∈fvMP[b≔N]
  lemma· M P PC→M PC→P _ | inj₁ a∈fvM[b≔N] with c∈xs++ys→c∈xs∨c∈ys {a} {fv M - b} {fv N} (PC→M a∈fvM[b≔N]) 
  ... | inj₂ a∈N = c∈xs∨c∈ys→c∈xs++ys {a} {fv (M · P) - b} {fv N} (inj₂ a∈N)
  ... | inj₁ a∈fvM-b with lemmafilter→ a (fv M) (λ y → not (⌊ b ≟ y ⌋)) a∈fvM-b
  ...   | px≡true , a∈fvM 
    = c∈xs∨c∈ys→c∈xs++ys {a} {fv (M · P) - b} {fv N} (inj₁ (lemmafilter← a (fv (M · P)) (λ y → not (⌊ b ≟ y ⌋)) px≡true (c∈xs∨c∈ys→c∈xs++ys {a} {fv M} {fv P} (inj₁ a∈fvM)))) 
  lemma· M P PC→M PC→P _ | inj₂ a∈fvP[b≔N] with c∈xs++ys→c∈xs∨c∈ys {a} {fv P - b} {fv N} (PC→P a∈fvP[b≔N]) 
  ... | inj₂ a∈N = c∈xs∨c∈ys→c∈xs++ys {a} {fv (M · P) - b} {fv N} (inj₂ a∈N)
  ... | inj₁ a∈fvP-b with lemmafilter→ a (fv P) (λ y → not (⌊ b ≟ y ⌋)) a∈fvP-b
  ...   | px≡true , a∈fvP
    = c∈xs∨c∈ys→c∈xs++ys {a} {fv (M · P) - b} {fv N} (inj₁ (lemmafilter← a (fv (M · P)) (λ y → not (⌊ b ≟ y ⌋)) px≡true (c∈xs∨c∈ys→c∈xs++ys {a} {fv M} {fv P} (inj₂ a∈fvP)))) 
  lemmaƛ : (M : Λ) (c : ℕ) → c ∉ a ∷ b ∷ fv N → PC→ a b N M → PC→ a b N (ƛ c M)
  lemmaƛ M c c∉abfvN PC→M a∈fvƛcM[b≔N] with c∈xs++ys→c∈xs∨c∈ys {a} {fv M - b} {fv N} (PC→M (lemma∈fvƛbM→a∈fvM {a} {c} {M [ b ≔ N ]} a≢c a∈fvƛcM[b≔N]'))
    where 
    a≢c : a ≢ c
    a≢c = λ a≡c → ⊥-elim (c∉abfvN (here (sym a≡c)))
    c∉b∷fvN : c ∉ b ∷ fv N
    c∉b∷fvN = λ c∈b∷fvN → ⊥-elim (c∉abfvN (there c∈b∷fvN))
    a∈fvƛcM[b≔N]' : a ∈ fv (ƛ c (M [ b ≔ N ]))
    a∈fvƛcM[b≔N]' rewrite sym (lemma∼αfv (lemmaƛ∼[] {b} {c} {N} M c∉b∷fvN)) = a∈fvƛcM[b≔N]
  ... | inj₂ a∈N = c∈xs∨c∈ys→c∈xs++ys {a} {fv (ƛ c M) - b} {fv N} (inj₂ a∈N)
  ... | inj₁ a∈fvM-b = c∈xs∨c∈ys→c∈xs++ys {a} {fv (ƛ c M) - b} {fv N} (inj₁ a∈fvƛcM-b)
    where
    px≡true = proj₁ (lemmafilter→ a (fv M) (λ y → not (⌊ b ≟ y ⌋)) a∈fvM-b)
    a∈fvM : a ∈ fv M
    a∈fvM = proj₂ (lemmafilter→ a (fv M) (λ y → not (⌊ b ≟ y ⌋)) a∈fvM-b)
    a≢c : a ≢ c
    a≢c = λ a≡c → ⊥-elim (c∉abfvN (here (sym a≡c)))
    a∈fvƛcM-b : a ∈ fv (ƛ c M) - b
    a∈fvƛcM-b = lemmafilter← a (fv (ƛ c M)) (λ y → not (⌊ b ≟ y ⌋)) px≡true (lemma∈fvM→a∈fvƛbM {a} {c} {M} a≢c a∈fvM)
\end{code}

\begin{code}
PC← : Atom → Atom → Λ → Λ → Set
PC← a b N M = b ∈ fv M → a ∈ fv N → a ∈ fv (M [ b ≔ N ])
\end{code}
