\begin{code}
module Permutation where

open import Atom
open import Term

open import Level
open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Properties
open import Data.List.Any.Membership
open Any.Membership-≡ renaming (_∈_ to _∈'_;_∉_ to _∉'_) 
open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _◻)
open import Algebra
open import Algebra.Structures

infixr 4 _∙_

Π = List (Atom × Atom)  
--
ι : List Atom
ι = [] 
--
_⁻¹ : Π → Π
_⁻¹ = reverse
--

\end{code}

%<*atomPermutation>
\begin{code}
_∙ₐ_ : Π → Atom → Atom
π ∙ₐ a = foldr (λ s b → （ proj₁ s ∙ proj₂ s ）ₐ b) a π 
\end{code}
%</atomPermutation>

%<*permutation>
\begin{code}
_∙_ : Π → Λ → Λ
π ∙ M = foldr (λ s M → （ proj₁ s ∙ proj₂ s ） M) M π 
\end{code}
%</permutation>

\begin{code}
atoms : Π → List Atom
atoms π = foldr (λ p r → proj₁ p ∷ proj₂ p ∷ r) [] π
--
lemmaπ∙π′∙M≡π++π′∙M : {π π′ : Π}{M : Λ} → (π ∙ (π′ ∙ M)) ≡ ((π ++ π′) ∙ M)
lemmaπ∙π′∙M≡π++π′∙M {[]}           {π′} {M} = refl
lemmaπ∙π′∙M≡π++π′∙M {(a , b) ∷ π}  {π′} {M} = cong (（_∙_）_ a b) (lemmaπ∙π′∙M≡π++π′∙M {π})
--
corollaryPπ++π′∙M→Pπ∙π′∙M : ∀ {π M} → {l : Level}{P : Λ → Set l} → ∀ π′ → P ((π′ ++ π) ∙ M) → P (π′ ∙ π ∙ M)
corollaryPπ++π′∙M→Pπ∙π′∙M {π} {M} {P} π′ Pπ′++πM 
  rewrite lemmaπ∙π′∙M≡π++π′∙M {π′} {π} {M} = Pπ′++πM 
--
lemmaπ⁻¹∘π≡id : {π : Π}{M : Λ} →  (π ⁻¹ ∙ π ∙ M) ≡ M
lemmaπ⁻¹∘π≡id {[]}           {M} = refl
lemmaπ⁻¹∘π≡id {(a , b) ∷ π}  {M} 
  = begin≡
      ((a , b) ∷ π) ⁻¹ ∙ ((a , b) ∷ π) ∙ M 
    ≡⟨ refl ⟩
      ((a , b) ∷ π) ⁻¹ ∙ （ a ∙ b ） (π ∙ M) 
    ≡⟨ cong (λ t → t ∙ （ a ∙ b ） (π ∙ M)) (unfold-reverse (a , b) π)  ⟩
      π ⁻¹ ++ [ (a , b) ] ∙ （ a ∙ b ） (π ∙ M) 
    ≡⟨ refl ⟩
      π ⁻¹ ++ [ (a , b) ] ∙ [ (a , b) ] ∙ (π ∙ M) 
    ≡⟨  lemmaπ∙π′∙M≡π++π′∙M {π ⁻¹ ++ [ (a , b) ]} ⟩
      (π ⁻¹ ++ [ (a , b) ]) ++ [ (a , b) ] ∙ (π ∙ M) 
    ≡⟨ cong (λ t → t ∙ (π ∙ M)) (++-assoc (π ⁻¹)  [ (a , b) ] [ (a , b) ]) ⟩
      π ⁻¹ ++ ([ (a , b) ] ++ [ (a , b) ]) ∙ (π ∙ M) 
    ≡⟨ refl ⟩
      π ⁻¹ ++ ( (a , b) ∷ (a , b) ∷ []) ∙ (π ∙ M) 
    ≡⟨ sym (lemmaπ∙π′∙M≡π++π′∙M {π ⁻¹})  ⟩
      π ⁻¹  ∙ （ a ∙ b ） （ a ∙ b ） (π ∙ M) 
    ≡⟨ cong (λ t → π ⁻¹  ∙ t) lemma（ab）（ab）M≡M ⟩
      π ⁻¹  ∙ π ∙ M
    ≡⟨ lemmaπ⁻¹∘π≡id {π} {M} ⟩
      M
    ◻
  where ++-assoc = IsSemigroup.assoc (IsMonoid.isSemigroup (Monoid.isMonoid (monoid (Atom × Atom))))
--
lemmaπ∙∣∣ : {M : Λ}{π : Π} → ∣ π ∙ M ∣ ≡ ∣ M ∣
lemmaπ∙∣∣ {M} {[]} = refl
lemmaπ∙∣∣ {M} {(a , b) ∷ π}  
  = begin≡
        ∣ ((a , b) ∷ π) ∙ M ∣ 
      ≡⟨ refl ⟩
        ∣ （ a ∙ b ） (π ∙ M) ∣ 
      ≡⟨ lemma∙∣∣ {π ∙ M}  ⟩
        ∣ π ∙ M ∣ 
      ≡⟨ lemmaπ∙∣∣ {M} {π} ⟩
        ∣ M ∣
    ◻ 
--
lemmaπ∙∣∣≤ : {M : Λ}{π : Π} → ∣ π ∙ M ∣ ≤′ ∣ M ∣
lemmaπ∙∣∣≤ {M} {π} rewrite lemmaπ∙∣∣ {M} {π} = ≤′-refl
--
lemmaπv : {a : Atom}{π : Π} → (π ∙ (v a)) ≡  v (π ∙ₐ a)
lemmaπv {a} {[]}     = refl
lemmaπv {a} {(b , c) ∷ π}  
  =  begin≡
        ((b , c) ∷ π ∙ v a) 
      ≡⟨ refl ⟩
        （ b ∙ c ） (π ∙ v a)
      ≡⟨ cong (（_∙_）_ b c) (lemmaπv {a} {π}) ⟩
        （ b ∙ c ） (v (π ∙ₐ a))
      ≡⟨ refl ⟩
        v (((b , c) ∷ π) ∙ₐ a)
      ◻
--
lemmaπ· : {M N : Λ}{π : Π} → (π ∙ (M · N)) ≡ (π ∙ M) · (π ∙ N)
lemmaπ· {M} {N} {[]} = refl
lemmaπ· {M} {N} {(a , b) ∷ π} 
  = begin≡
      ((a , b) ∷ π) ∙ (M · N) 
    ≡⟨ refl ⟩ 
      （ a ∙ b ） (π ∙ (M · N))
    ≡⟨ cong (（_∙_）_ a b) (lemmaπ· {M} {N} {π}) ⟩ 
      （ a ∙ b ） ((π ∙ M) · (π ∙ N))
    ≡⟨ refl ⟩ 

      (((a , b) ∷ π) ∙ M) · (((a , b) ∷ π) ∙ N)
    ◻
--
lemmaπƛ : {a : Atom}{M : Λ}{π : Π} → (π ∙ (ƛ a M)) ≡ ƛ (π ∙ₐ a) (π ∙ M)
lemmaπƛ {a} {M} {[]} = refl
lemmaπƛ {a} {M} {(b , c) ∷ π} 
 = begin≡
     ((b , c) ∷ π) ∙ ƛ a M  
   ≡⟨ refl ⟩
     （ b ∙ c ） (π ∙ ƛ a M)
   ≡⟨ cong (（_∙_）_ b c) (lemmaπƛ {a} {M} {π}) ⟩ 
     （ b ∙ c ） (ƛ (π ∙ₐ a)  (π ∙ M))
   ≡⟨ refl ⟩
     ƛ (((b , c) ∷ π) ∙ₐ a) (((b , c) ∷ π) ∙ M)
   ◻
--
lemmaπ∙ₐ≡ : {a : Atom}{π : Π} → a ∉' atoms π → π ∙ₐ a ≡ a
lemmaπ∙ₐ≡ {a} {[]}           a∉π  = refl
lemmaπ∙ₐ≡ {a} {(b , c) ∷ π}  a∉b,c∷π 
  rewrite lemmaπ∙ₐ≡ {a} {π} (λ a∈π → a∉b,c∷π (there (there a∈π))) 
  with a ≟ₐ b 
... | no _ with a ≟ₐ c
...        | no _                 = refl
lemmaπ∙ₐ≡ {a} {(b , .a) ∷ π}  a∉b,a∷π 
    | no _ | yes refl             
    = ⊥-elim (a∉b,a∷π (there (here refl)))
lemmaπ∙ₐ≡ {a} {(.a , c) ∷ π}  a∉a,c∷π   
    | yes refl                    
    = ⊥-elim (a∉a,c∷π (here refl))
--
lemmaπ∙distributive : {a b : Atom}{M : Λ}{π : Π} → (π ∙ （ a ∙ b ） M) ≡ (（ π ∙ₐ a ∙ π ∙ₐ b ） (π ∙ M))
lemmaπ∙distributive {a} {b} {M} {[]} = refl
lemmaπ∙distributive {a} {b} {M} {(c , d) ∷ π} 
  rewrite lemmaπ∙distributive {a} {b} {M} {π}  
  |       lemma∙distributive {c} {d} {π ∙ₐ a} {π ∙ₐ b} {π ∙ M}
  = refl
--
lemmaππ∙ₐinj : {a b : Atom}{π : Π} → a ≢ b → π ∙ₐ a ≢ π ∙ₐ b
lemmaππ∙ₐinj {a} {b} {[]}           a≢b = a≢b
lemmaππ∙ₐinj {a} {b} {(c , d) ∷ π}  a≢b = lemma∙ₐinj (lemmaππ∙ₐinj {π = π} a≢b)
\end{code}
