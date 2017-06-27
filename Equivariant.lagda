\begin{code}
module Equivariant where

open import Atom
open import Term
open import Permutation

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

EquivariantRel : (Λ → Λ → Set) → Set
EquivariantRel R = {M N : Λ}(π : Π) → R M N → R (π ∙ M) (π ∙ N)
--
EquivariantRel← : (Λ → Λ → Set) → Set
EquivariantRel← R = {M N : Λ}(π : Π) → R (π ∙ M) (π ∙ N) → R M N
--
lemmaEqRel : (R : Λ → Λ → Set) → EquivariantRel R → EquivariantRel← R
lemmaEqRel R EqR {M} {N} π RπMπN 
  with EqR (π ⁻¹) RπMπN 
... | Rπ⁻¹πMπ⁻¹πN rewrite lemmaπ⁻¹∘π≡id {π} {M} | lemmaπ⁻¹∘π≡id {π} {N} 
  = Rπ⁻¹πMπ⁻¹πN
--
EquivariantRela : (Atom → Λ → Set) → Set
EquivariantRela R = {a : Atom}{M : Λ}(π : Π) → R a M → R (π ∙ₐ a) (π ∙ M)
--
lemma#Equiv : EquivariantRela _#_
lemma#Equiv {a} .{v b}    π (#v {b} b≢a) 
  rewrite lemmaπv {b} {π} 
  = #v (lemmaππ∙ₐinj {b} {a} {π} b≢a)
lemma#Equiv {a} .{M · N}  π (#· {M} {N} a#M a#N) 
  rewrite lemmaπ· {M} {N} {π}
  = #· (lemma#Equiv π a#M) (lemma#Equiv π a#N)
lemma#Equiv {a} .{ƛ a M}  π (#ƛ≡ {M}) 
  rewrite lemmaπƛ {a} {M} {π} 
  = #ƛ≡
lemma#Equiv {a} {ƛ b M}   π (#ƛ a#M)
  rewrite lemmaπƛ {b} {M} {π} 
  = #ƛ (lemma#Equiv π a#M)
--
lemma∉swap : {a b c : Atom}{M : Λ} → a ∉ₜ M → （ b ∙ c ）ₐ a ∉ₜ （ b ∙ c ） M 
lemma∉swap {a} {b} {c}   {M} a∉M with b ≟ₐ c 
lemma∉swap {a} {b} {.b}  {M} a∉M
  | yes refl rewrite lemma（aa）M≡M {b} {M} | lemma（aa）b≡b {b} {a} 
  = a∉M 
lemma∉swap {a} {b} {c} {v d} (∉v d≢a) | no b≢c        = ∉v (lemma∙ₐinj d≢a)
lemma∉swap {a} {b} {c} {M · N} (∉· a∉M a∉N) | no b≢c  = ∉· (lemma∉swap a∉M) (lemma∉swap a∉N)
lemma∉swap {a} {b} {c} {ƛ d M} (∉ƛ d≢a a∉M) | no b≢c  = ∉ƛ (lemma∙ₐinj d≢a) (lemma∉swap a∉M)
\end{code}


