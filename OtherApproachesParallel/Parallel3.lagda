\begin{code}
module Parallel3 where

open import Level
open import Function
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
open import Substitution

open import Data.Bool hiding (_∨_)
open import Data.Nat hiding (_*_)
open import Data.Nat.Properties
open import Data.Empty
open import Data.Sum -- renaming (_⊎_ to _∨_)
open import Data.List
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ)
open import Relation.Nullary
open import Relation.Nullary.Decidable
\end{code}

Parallel reduction.

%<*parallel>
\begin{code}
⇉hv : Atom → Λ → Set
⇉hv a M = v a ≡ M

⇉h·v : (Λ → Set) → (Λ → Set) → Atom → Set
⇉h·v r1 r2 a = ∃ (λ x → ∃ (λ P →   ∃ (λ Q → r1 (ƛ x P) × r2 Q × v a ≡ P [ x ≔ Q ])))  

⇉h·· : (Λ → Set) → (Λ → Set) → Set → Set → Λ → Λ → Set
⇉h·· r1 r2 _ _ P Q =  (r1 P × r2 Q) ⊎ 
                      ∃ (λ x → ∃ (λ P' →  ∃ (λ Q' → r1 (ƛ x P') × r2 Q' × P · Q ∼α P' [ x ≔ Q' ])))  -- identico o alfa ????

⇉h·ƛ : (Λ → Set) → (Λ → Set) → Atom → Set → Λ → Set
⇉h·ƛ r1 r2 a _ M = ∃ (λ x → ∃ (λ P' →  ∃ (λ Q' → r1 (ƛ x P') × r2 Q' × ƛ a M ∼α P' [ x ≔ Q' ])))

⇉h· : (Λ → Set) → (Λ → Set) → Λ → Set
⇉h· r1 r2 = ΛRec Set (⇉h·v r1 r2) (⇉h·· r1 r2) ([] , (⇉h·ƛ r1 r2)) 

⇉h·αcompatible : {f g : Λ → Set}{M N : Λ} → M ∼α N → ⇉h· f g M ≡ ⇉h· f g N
⇉h·αcompatible {f} {g} {M} {N} M∼N 
  rewrite lemmaΛRecStrongαCompatible Set (⇉h·v f g) (⇉h·· f g) ([] , (⇉h·ƛ f g)) M N M∼N = refl

⇉hƛ : Atom → (Λ → Set) → Λ → Set
⇉hƛ a r = ΛRec Set (const ⊥) (λ _ _ _ _ → ⊥) ([] , (λ b _ M → r (（ b ∙ a ） M))) 

⇉hƛαcompatible : {a : Atom}{f : Λ → Set}{M N : Λ} → M ∼α N → ⇉hƛ a f M ≡ ⇉hƛ a f N
⇉hƛαcompatible {a} {f} {M} {N} M∼N
  rewrite lemmaΛRecStrongαCompatible Set (const ⊥) (λ _ _ _ _ → ⊥) ([] , (λ b _ M → f (（ b ∙ a ） M))) M N M∼N = refl
  
⇉hƛv : (a b : Atom)(f : Λ → Set) → ⇉hƛ a f (v b) ≡ ⊥
⇉hƛv a b f 
  rewrite ΛRecv Set (const ⊥) (λ _ _ _ _ → ⊥) [] (λ b _ M → f (（ b ∙ a ） M)) b = refl

⇉hƛ· : (a : Atom)(f : Λ → Set)(M N : Λ) → ⇉hƛ a f (M · N) ≡ ⊥
⇉hƛ· a f M N 
  rewrite ΛRec· Set (const ⊥) (λ _ _ _ _ → ⊥) [] (λ b _ M → f (（ b ∙ a ） M)) M N = refl

⇉hƛƛ :  (a b : Atom)(f : Λ → Set)(M : Λ) 
        → ∃ (λ N →  （ b ∙ χ [] (ƛ b M) ） M ∼α  N   × 
                    ⇉hƛ a f (ƛ b M) ≡ f (（ χ [] (ƛ b M) ∙ a ） N)) 
⇉hƛƛ a b f M = ΛRecƛ' Set (const ⊥) (λ _ _ _ _ → ⊥) [] (λ b _ M → f (（ b ∙ a ） M)) b M 

infix 4 _⇉_
_⇉_ : Λ → Λ → Set
_⇉_ = ΛRec (Λ → Set) ⇉hv ⇉h· ([] , ⇉hƛ)
\end{code}
%</parallel>

