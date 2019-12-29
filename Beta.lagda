\begin{code}
module Beta where

open import Atom
open import Chi
open import Term
open import Substitution
open import Alpha
open import Relation Λ hiding (_++_) renaming (_⊆_ to _⊆R_)
open import NaturalProperties

open import ListProperties

open import Data.Empty
open import Data.Sum
open import Data.Nat hiding (_*_)
open import Relation.Nullary
open import Relation.Binary hiding (Rel)
open import Function hiding (_∘_)
open import Data.Product renaming (Σ to Σₓ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂; setoid)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _◻)
open import Data.List hiding (any) renaming (length to length') 
open import Data.List.Properties
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡ hiding (_⊆_)

infix   1 _▹_ 
\end{code}

Beta contraction

%<*betacontraction>
\begin{code}
data _▹_ : Λ → Λ → Set where
  ▹β  :  {M N : Λ}{x : Atom} 
      →  ƛ x M · N ▹ M [ x ≔ N ]
\end{code}
%</betacontraction>

Beta contraction preserves typing judge.

Context clousure of beta contraction.

\end{code}

%<*beta>
\begin{code}
data ctx (r : Rel) : Rel where
  ctxinj : ∀ {t t'}       → r t t'        → ctx r t t'
  ctx·l  : ∀ {t₁ t₁' t₂}  → ctx r t₁ t₁'  → ctx r (t₁ · t₂) (t₁' · t₂)
  ctx·r  : ∀ {t₁ t₂ t₂'}  → ctx r t₂ t₂'  → ctx r (t₁ · t₂) (t₁ · t₂')
  ctxƛ   : ∀ {x t₁ t₁'}   → ctx r t₁ t₁'  → ctx r (ƛ x t₁) (ƛ x t₁')

infix 4 _→β_
_→β_ : Rel
_→β_ = ctx _▹_
\end{code}
%</beta>


%<*alphabeta>
\begin{code}
infix 4 _→α_ 
_→α_ : Rel
_→α_ = _→β_ ∪ _∼α_
\end{code}
%</alphabeta>

%<*asteralphabeta>
\begin{code}
infix 4 _→α*_
_→α*_ : Rel
_→α*_ = star _→α_
\end{code}
%</asteralphabeta>

\begin{code}
abs-step : ∀ {x t t'} → t →α t' → ƛ x t →α ƛ x t'
abs-step (inj₁ M→βN) = inj₁ (ctxƛ M→βN)
abs-step (inj₂ M∼N)  = inj₂ (lemma∼αƛ M∼N) 

abs-star : ∀ {x M N} → M →α* N → ƛ x M →α* ƛ x N
abs-star refl                 = refl
abs-star (just M→αN)          = just   (abs-step M→αN) 
abs-star (trans M→α*N N→α*P)  = trans  (abs-star M→α*N) (abs-star N→α*P)

app-step-l : ∀ {M N P} → M →α P  → M · N →α P · N
app-step-l (inj₁ t→t') = inj₁ (ctx·l t→t')
app-step-l (inj₂ t∼t') = inj₂ (∼α· t∼t' ρ)

app-step-r : ∀ {M N P} → N →α P → M · N →α M · P
app-step-r (inj₁ t→t') = inj₁ (ctx·r t→t')
app-step-r (inj₂ t∼t') = inj₂ (∼α· ρ t∼t')

app-star-l : ∀ {M N P} → M →α* P → M · N →α* P · N
app-star-l refl                     = refl
app-star-l (just x)                 = just (app-step-l x)
app-star-l (trans t→α*t' t'→α*t'')  = trans (app-star-l t→α*t') (app-star-l t'→α*t'')

app-star-r : ∀ {M N P} → N →α* P → M · N →α* M · P
app-star-r refl                     = refl
app-star-r (just t→α*t')            = just (app-step-r t→α*t')
app-star-r (trans t→α*t' t'→α*t'')  = trans (app-star-r t→α*t') (app-star-r t'→α*t'')

app-star : ∀ {M M' N N'} → M →α* M' → N →α* N' → M · N →α* M' · N'
app-star M→α*M' N→α*N' = trans (app-star-l M→α*M') (app-star-r N→α*N')

β-star : ∀ {x M N } → ƛ x M · N →α* M [ x ≔ N ]
β-star = just (inj₁ (ctxinj ▹β))
\end{code}

Reduction is a preorder over terms, hence we can use the combinators of
the standard library for proving the reduction of a term to another.

\begin{code}
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality renaming (sym to sym';trans to trans')
open import Relation.Binary using (Preorder)
import Relation.Binary.PreorderReasoning as PreR    

→-preorder : Preorder _ _ _
→-preorder =  
    record { 
      Carrier = Λ;
      _≈_ = _≡_;
      _∼_ = _→α*_;
      isPreorder =  record {
        isEquivalence = Relation.Binary.Setoid.isEquivalence (PropEq.setoid Λ) ;
        reflexive = λ { {M} {.M} refl → refl};
        trans = star.trans } 
    }

open PreR →-preorder renaming (begin_ to begin→_;_∼⟨_⟩_ to _→⟨_⟩_;_≈⟨_⟩_ to _=⟨_⟩_;_∎ to _▣) public
\end{code}

-- \begin{code}
-- lemma▹* : {x : Atom} → (_*_ x) preserved-by (dual _▹_) 
-- lemma▹* {x} .{M [ y ≔ N ]} {ƛ y M · N} x*M[x≔N] ▹β
--   = {!!}

-- lemma→α* : {x : Atom} → (_*_ x) preserved-by (dual _→β_) 
-- lemma→α* x*N           (ctxinj ▹β)   = lemma▹* x*N ▹β
-- lemma→α* (*·l x*N)     (ctx·l M→βN)  = *·l (lemma→α* x*N M→βN)
-- lemma→α* (*·r x*N')    (ctx·l M→βN)  = *·r x*N'
-- lemma→α* (*·l x*N)     (ctx·r M→βN)  = *·l x*N
-- lemma→α* (*·r x*N')    (ctx·r M→βN)  = *·r (lemma→α* x*N' M→βN)
-- lemma→α* (*ƛ x*N y≢x)  (ctxƛ M→βN)   = *ƛ (lemma→α* x*N M→βN) y≢x

-- lemma→β# : {x : Atom} → (_#_ x) preserved-by (_→β_) 
-- lemma→β# = {!!} --dual-*-# lemma→α*

-- lemma→α# : {x : Atom} → (_#_ x) preserved-by (_→α_) 
-- lemma→α#      x#M (inj₁ M→βN)  = lemma→β# x#M M→βN
-- lemma→α# {x}  x#M (inj₂ M~N)   = {!!} -- lemmaM∼N# M~N x x#M

-- lemma→α*# : {x : Atom} → (_#_ x) preserved-by (_→α*_)
-- lemma→α*# x#M refl                 = x#M 
-- lemma→α*# x#M (just M→αN)          = lemma→α# x#M M→αN
-- lemma→α*# x#M (trans M→α*P P→α*N)  = lemma→α*# (lemma→α*# x#M M→α*P) P→α*N
-- \end{code}

-- Subject Reduction

-- \begin{code}
-- lemma⊢→α* :  {Γ : Cxt}{α : Type}{M N : Λ} 
--              → Γ ⊢ M ∶ α → M →α* N → Γ ⊢ N ∶ α
-- lemma⊢→α* Γ⊢M:α refl                  = Γ⊢M:α
-- lemma⊢→α* Γ⊢M:α (just M→βN)           = lemma⊢→α Γ⊢M:α M→βN
-- lemma⊢→α* Γ⊢M:α (trans M→α*N N→α*P)   = lemma⊢→α* (lemma⊢→α* Γ⊢M:α M→α*N) N→α*P
-- \end{code}









