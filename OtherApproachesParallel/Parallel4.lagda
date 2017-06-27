\begin{code}
module Parallel4 where

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
abstract
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

  infix 4 _⇉_
  _⇉_ : Λ → Λ → Set
  _⇉_ = ΛIt (Λ → Set) ⇉hv ⇉h· ([] , ⇉hƛ)
\end{code}
%</parallel>

-- \begin{code}
--   lemma⇉αleft : {M N P : Λ} → M ∼α N → N ⇉ P → M ⇉ P
--   lemma⇉αleft {M} {N} {P} M∼N N⇉P 
--     rewrite lemmaΛItStrongαCompatible (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ M N M∼N = N⇉P
-- \end{code}

-- \begin{code}
--   lemma⇉Equiv#Left : {a b : Atom}{M N : Λ} → a # M → b # M → M ⇉ N → （ a ∙ b ） M ⇉ N
--   lemma⇉Equiv#Left {a} {b} {M} a#M b#M M⇉N rewrite lemmaΛItEquiv# (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ M a b a#M b#M 
--     = M⇉N 
-- \end{code}

-- \begin{code}
--   lemma⇉αright : {M N P : Λ} → M ⇉ N → N ∼α P → M ⇉ P
--   lemma⇉αright {v x}             x⇉N   N∼P     
--     rewrite ΛItv (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ x 
--     with x⇉N | N∼P
--   ... | refl | ∼αv = refl
--   lemma⇉αright {M · M'}          MM'⇉N  N∼P 
--     rewrite  ΛIt· (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ M M'
--     |        ⇉h·αcompatible {ΛIt (Λ → Set) ⇉hv ⇉h· ([] , ⇉hƛ) M} {ΛIt (Λ → Set) ⇉hv ⇉h· ([] , ⇉hƛ) M'} N∼P 
--     = MM'⇉N
--   lemma⇉αright {ƛ x M}  {N} {P}  ƛxM⇉N  N∼P   
--     rewrite ΛItƛ (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ x M 
--     |       ⇉hƛαcompatible {χ [] (ƛ x M)} {ΛIt (Λ → Set) ⇉hv ⇉h· ([] , ⇉hƛ) ([ (x , (χ [] (ƛ x M))) ] ∙ M)} {N} {P} N∼P 
--     = ƛxM⇉N
-- \end{code}

-- \begin{code}
--   lemma⇉Equiv#Right : {a b : Atom}{M N : Λ} → a # N → b # N → M ⇉ N → M ⇉ （ a ∙ b ） N
--   lemma⇉Equiv#Right {a} {b} {M} {N} a#N b#N M⇉N = lemma⇉αright {M} {N} {（ a ∙ b ） N} M⇉N (lemma#∼α {a} {b} {N} a#N b#N)
-- \end{code}

-- Parallel reduction destructors.

-- \begin{code}
--   lemma⇉v :  {x : Atom}{M : Λ} → v x ⇉ M → M ≡ v x
--   lemma⇉v {x} vx⇉M 
--     rewrite ΛItv (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ x 
--     with vx⇉M
--   ... | refl = refl
-- \end{code}

-- \begin{code}
--   lemma⇉· :  {M N P : Λ} 
--              → M · N ⇉ P 
--              → ∃ (λ P' → ∃ λ P'' → P ∼α P' · P'' × M ⇉ P' × N ⇉ P'')   ⊎ 
--                ∃ (λ x → ∃ (λ M'  → M ⇉ ƛ x M' × ∃ (λ N' → N ⇉ N' × P ∼α M' [ x ≔ N' ])))  
--   lemma⇉· {M} {N} {P = ƛ x P} MN⇉ƛxP rewrite ΛIt· (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ M N
--     with ΛRecƛ' Set (⇉h·v (_⇉_ M) (_⇉_ N)) (⇉h·· (_⇉_ M) (_⇉_ N)) []  (⇉h·ƛ (_⇉_ M) (_⇉_ N)) x P 
--   ... | (Q , （x∙χ）P∼Q , MN⇉a) rewrite MN⇉a with MN⇉ƛxP 
--   ... | (y , R , R' , M⇉ƛyR , N⇉R' , ƛχQ∼R[y≔R'])
--     = inj₂ (y , R , M⇉ƛyR , R' , N⇉R' , τ (τ (lemma∼λχ {x} {[]} {P}) (lemma∼αƛ （x∙χ）P∼Q)) ƛχQ∼R[y≔R'])  -- λxP∼R[x≔R'] 
--   lemma⇉· {M} {N} {P = v x} MN⇉x
--     rewrite ΛIt· (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ M N
--     |       ΛRecv Set (⇉h·v (_⇉_ M) (_⇉_ N)) (⇉h·· (_⇉_ M) (_⇉_ N)) []  (⇉h·ƛ (_⇉_ M) (_⇉_ N)) x
--     with MN⇉x
--   ... | (y , M' , N' , M⇉λyM' , N⇉N' , P≡M'[y≔N'] ) =  inj₂ (y , M' , M⇉λyM' , N' , N⇉N' , lemma≡→∼ P≡M'[y≔N']) -- aca ≡
--   lemma⇉· {M} {N} {P = P · P'} MN⇉PP'
--     rewrite ΛIt· (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ M N
--     with ΛRec·' Set (⇉h·v (_⇉_ M) (_⇉_ N)) (⇉h·· (_⇉_ M) (_⇉_ N)) []  (⇉h·ƛ (_⇉_ M) (_⇉_ N)) P P' 
--   ...  | (Q , Q' , P∼Q , P'∼Q' , MN⇉a) rewrite MN⇉a with MN⇉PP' 
--   ...  | inj₁ (M⇉Q , N⇉Q') 
--     = inj₁ (Q , Q' , ∼α· P∼Q P'∼Q' , M⇉Q , N⇉Q') 
--   ...  | inj₂ (x , R , R' , M⇉ƛxR , N⇉R' , QQ'∼R[x≔R']) 
--     = inj₂ (x , R , M⇉ƛxR , R' , N⇉R' , τ (∼α· P∼Q P'∼Q') QQ'∼R[x≔R'])
-- \end{code}

-- \begin{code}
--   lemma⇉ƛ :  {x : Atom}{M N : Λ} 
--              → ƛ x M ⇉ N
--              → ∃ (λ y → ∃ (λ P → N ∼α ƛ y P × （ x ∙ χ [] (ƛ x M) ） M ⇉ （ y ∙ χ [] (ƛ x M) ） P))
--   lemma⇉ƛ {x} {M} {v y}     ƛxM⇉N 
--     rewrite ΛItƛ (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ x M 
--     |       ΛRecv Set (const ⊥) (λ _ _ _ _ → ⊥) [] (λ b _ Q → (_⇉_ (（ x ∙ χ [] (ƛ x M) ） M) (（ b ∙ χ [] (ƛ x M) ） Q))) y 
--     with ƛxM⇉N 
--   ... | ()
--   lemma⇉ƛ {x} {M} {N · N'}  ƛxM⇉NN'
--     rewrite ΛItƛ (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ x M 
--     |       ΛRec· Set (const ⊥) (λ _ _ _ _ → ⊥) [] (λ b _ Q → (_⇉_ (（ x ∙ χ [] (ƛ x M) ） M) (（ b ∙ χ [] (ƛ x M) ） Q))) N N'
--     with ƛxM⇉NN'
--   ... | ()
--   lemma⇉ƛ {x} {M} {ƛ y N}   ƛxM⇉ƛyN 
--     rewrite ΛItƛ (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ x M 
--     with ΛRecƛ' Set (const ⊥) (λ _ _ _ _ → ⊥) [] (λ b _ Q → (_⇉_ (（ x ∙ χ [] (ƛ x M) ） M) (（ b ∙ χ [] (ƛ x M) ） Q))) y N
--   ... | (P , （y∙χy）N∼P ,  ƛxM⇉ƛyN≡（x∙χx）M⇉（χy∙χx）P)
--     rewrite ƛxM⇉ƛyN≡（x∙χx）M⇉（χy∙χx）P
--     = χ [] (ƛ y N) , P ,  τ (lemma∼λχ {y} {[]} {N}) (lemma∼αƛ （y∙χy）N∼P) ,  ƛxM⇉ƛyN 
-- \end{code}

-- Parallel reduction constructors.

-- \begin{code}
--   lemma⇉vc :  {x : Atom} → v x ⇉ v x
--   lemma⇉vc {x} 
--     rewrite ΛItv (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ x 
--     = refl
-- \end{code}


-- \begin{code}
--   lemma⇉ƛc :  {x y : Atom}{M N P : Λ} 
--               → N ∼α ƛ y P → （ x ∙ χ [] (ƛ x M) ） M ⇉ （ y ∙ χ [] (ƛ x M) ） P
--               → ƛ x M ⇉ N
--   lemma⇉ƛc {x} .{z} {M} .{ƛ y N} .{P} (∼αƛ {N} {P} {y} {z} xs f) （x∙χ）M⇉（z∙χ）P 
--     rewrite ΛItƛ (Λ → Set) ⇉hv ⇉h· [] ⇉hƛ x M 
--     with ΛRecƛ' Set (const ⊥) (λ _ _ _ _ → ⊥) [] (λ b _ Q → (_⇉_ (（ x ∙ χ [] (ƛ x M) ） M) (（ b ∙ χ [] (ƛ x M) ） Q))) y N
--   ... | (Q , （y∙χy）N∼Q ,  ƛxM⇉ƛyN≡（x∙χx）M⇉（χy∙χx）Q)
--     rewrite ƛxM⇉ƛyN≡（x∙χx）M⇉（χy∙χx）Q
--     = lemma⇉αright  （x∙χ）M⇉（z∙χ）P  
--                     (begin
--                       （ z ∙ χx ） P
--                     ∼⟨ {!!} ⟩
--                       （ w ∙ χx ） （ z ∙ w ） P
--                     ∼⟨ {! !} ⟩
--                       （ w ∙ χx ） （ χy ∙ w ） Q
--                     ∼⟨ {!!} ⟩
--                       （ χy ∙ χx ） Q
--                     ∎) -- z∙χx P ∼ χy∙χx Q 
--     where 
--     χx : Atom
--     χx = χ [] (ƛ x M)
--     χy : Atom
--     χy = χ [] (ƛ y N)
--     w : Atom
--     w = χ xs (ƛ y N)
--     w∉xs : w ∉ xs
--     w∉xs = χ∉ xs (ƛ y N)
--     w#ƛyN : w # ƛ y N
--     w#ƛyN = χ# xs (ƛ y N)
-- -- w not in xs → (y w) N ∼ (z w) P y (y w) N ~ (χy w) Q entonces (z w) P ~ (χy w) Q 
-- \end{code}
