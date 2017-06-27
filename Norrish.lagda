\begin{code}
module Norrish where

open import Atom
open import Term hiding (fv)
open import TermRecursion
open import ListProperties

open import Data.Nat hiding (equal)
open import Data.Bool
open import Data.List
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open import Data.Maybe hiding (map)
open import Data.Product hiding (map)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary.PropositionalEquality as PropEq  hiding ([_]) 
\end{code}

Norrish functions.

\begin{code}
idΛ : Λ → Λ
idΛ = ΛIt Λ v _·_ ([] , ƛ)
\end{code}

%<*constructors>
\begin{code}
isVar : Λ → Maybe Atom
isVar = ΛIt  (Maybe Atom) 
             just 
             (λ _ _ → nothing) 
             ([] , λ _ _ → nothing)
--
isApp : Λ → Maybe (Λ × Λ)
isApp = ΛRec  (Maybe (Λ × Λ)) 
              (λ _ → nothing) 
              (λ _ _ M N → just (M , N)) 
              ([] , λ _ _ _ → nothing)
--
isAbs : Λ → Maybe (Atom × Λ)
isAbs = ΛRec  (Maybe (Atom × Λ)) 
              (λ _ → nothing) (λ _ _ _ _ → nothing) 
              ([] , λ a _ M → just (a , M))
\end{code}
%</constructors>

%<*size>
\begin{code}
size : Λ → ℕ
size = ΛIt ℕ (const 1) (λ n m → suc n + m) ( [] , λ _ n → suc n)
\end{code}
%</size>

Size tests:
\begin{code}
size1 : size (ƛ 1 ((v 1) · (v 2))) ≡ 4
size1 = refl
--
size2 : size (v 1) ≡ 1
size2 = refl
\end{code}

Alpha equality decidibility

%<*alphaEqual>
\begin{code}
equal : Λ → Λ → Bool
equal = ΛIt (Λ → Bool) vareq appeq ([] , abseq)
  where
  vareq : Atom → Λ → Bool
  vareq a M with isVar M
  ... | nothing  = false
  ... | just b   = ⌊ a ≟ₐ b ⌋
  appeq : (Λ → Bool) → (Λ → Bool) → Λ → Bool
  appeq fM fN P with isApp P
  ... | nothing         = false
  ... | just (M' , N')  = fM M' ∧ fN N'
  abseq : Atom → (Λ → Bool) → Λ → Bool
  abseq a fM N with isAbs N
  ... | nothing = false
  ... | just (b , P) = ⌊ a ≟ₐ b ⌋ ∧ fM P 
\end{code}
%</alphaEqual>

Observe that $\AgdaFunction{isAbs}$\ function also normalises $\AgdaBound{N}$, so it is correct in the last line to ask if the two variable binders are equal.

Some tests:

\begin{code}
equal1 : equal ((ƛ 1 (v 1)) · (v 1)) ((ƛ 2 (v 2)) · (v 1)) ≡ true
equal1 = refl
--
equal2 : equal ((ƛ 1 (v 1)) · (v 2)) ((ƛ 2 (v 2)) · (v 1)) ≡ false
equal2 = refl
\end{code}

Another way to do decide alfa equality, is decide syntatical equality over terms, then using idTerm we can normalise the parameters, and then check for syntactical equality between normalised terms.

\begin{code}
synEqual : Λ → Λ → Bool
synEqual (v a)    (v b) = ⌊ a ≟ₐ b ⌋
synEqual (v a)    (_ · _)  = false
synEqual (v a)    (ƛ _ _)  = false
synEqual (M · N)  (v _)    = false
synEqual (M · N)  (P · Q)  = synEqual M P ∧ synEqual N Q
synEqual (M · N)  (ƛ x P)  = false
synEqual (ƛ a M)  (v _)    = false
synEqual (ƛ a M)  (_ · _)  = false
synEqual (ƛ a M)  (ƛ b N)  = ⌊ a ≟ₐ b ⌋ ∧ synEqual M N
--
equal' : Λ → Λ → Bool
equal' M N = synEqual (idΛ M) (idΛ N)
\end{code}

Some tests:

\begin{code}
equal'1 : equal' ((ƛ 1 (v 1)) · (v 1)) ((ƛ 2 (v 2)) · (v 1)) ≡ true
equal'1 = refl
--
equal'2 : equal' ((ƛ 1 (v 1)) · (v 2)) ((ƛ 2 (v 2)) · (v 1)) ≡ false
equal'2 = refl
\end{code}


\begin{code}
fv : Λ → List Atom
fv = ΛIt (List Atom) [_] _++_ ([] , λ v r → r - v)
--
infix 3 _∈b_
_∈b_ : Atom → List Atom → Bool
a ∈b as = ⌊ Any.any (_≟ₐ_ a) as ⌋
--
infix 2 _⇒_
\end{code}

%<*enf>
\begin{code}
_⇒_ : Bool → Bool → Bool
false  ⇒ b = true
true   ⇒ b = b
--
enf : Λ → Bool
enf = ΛRec Bool (const true) (λ b1 b2 _ _ → b1 ∧ b2) ([] , absenf)
  where
  absenf : Atom → Bool → Λ → Bool
  absenf a b M with isApp M
  ... | nothing = b
  ... | just (P , Q) = b ∧ (equal Q (v a) ⇒ a ∈b (fv P))
\end{code}
%</enf>


%<*vposns>
\begin{code}
data Direction : Set where
  Lt Rt In : Direction
--
vposns : Atom → Λ → List (List Direction)
vposns a = ΛIt (List (List Direction)) varvposns appvposns ([ a ] , absvposns)
  where
  varvposns : Atom → List (List Direction)
  varvposns b with a ≟ₐ b 
  ... | yes  _ = [ [] ]
  ... | no   _ = [] 
  appvposns : List (List Direction) → List (List Direction) 
            → List (List Direction)
  appvposns l r = map (_∷_ Lt) l ++ map (_∷_ Rt) r
  absvposns : Atom → List (List Direction) → List (List Direction)
  absvposns a r = map (_∷_ In) r
\end{code}
%</vposns>

Test : v_posns 2 (ƛ 2 ((v 2) · (v 3)))

%<*sub>
\begin{code}
hvar : Atom → Atom → Λ → Λ
hvar x y with x ≟ₐ y
... | yes _ = id
... | no  _ = λ _ → (v y)
--
sub' : Atom → Λ → Λ → Λ
sub' x M P = ΛIt  (Λ → Λ) 
                  (hvar x) 
                  (λ f g N →  f N · g N) 
                  (x ∷ 0 ∷ fv P , λ a f N → ƛ a (f ((v 0) · N))) 
                  M P
\end{code}
%</sub>

Tests:
 sub' 2 (ƛ 3 ((v 3) · (v 2))) (v 3)
 sub' 2 (ƛ 4 (ƛ 3 ((v 3) · (v 2)))) (v 3)
