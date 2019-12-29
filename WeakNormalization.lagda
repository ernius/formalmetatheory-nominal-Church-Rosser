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

open import Induction.WellFounded
open import Data.Bool hiding (_∨_;_≟_)
open import Data.Product renaming (Σ to Σₓ;map to mapₓ;_,_ to _∶_) public
open import Data.Sum renaming (_⊎_ to _∨_;map to map+)
open import Data.Empty
open import Data.Product renaming (Σ to Σₓ;map to mapₓ;_,_ to _∶_) public
open import Function hiding (_⟨_⟩_)
open import Relation.Nullary 
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_]) renaming (trans to trans≡)
open import Data.List hiding ([_])
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡  renaming (_∈_ to _∈l_;_⊆_ to _⊆l_;_∉_ to _∉l_)
open import Data.List.Any.Properties
\end{code}


\begin{code}
infix 4 _<'_

data _<'_ : Type → Type → Set where
  <l : ∀ {α β} → α <' α ⟶ β
  <r : ∀ {α β} → β <' α ⟶ β

open Transitive-closure _<'_ renaming (_<⁺_ to _<_) 

infixl 10 _≤_

_≤_ : Type → Type → Set
α ≤ β = α < β ∨ α ≡ β

Acc< : Type → Set
Acc< = Acc _<_

wf<' : Well-founded _<'_
wf<' τ = acc λ y ()
wf<' (α ⟶ β) = acc accind
  where accind : (γ : Type) → γ <' (α ⟶ β) → Acc _<'_ γ
        accind .α <l = wf<' α
        accind .β <r = wf<' β

wf< : Well-founded _<_
wf< = well-founded wf<'

γ⟶α≤β→γ<β : ∀ {γ α β} → (γ ⟶ α) ≤ β → γ < β
γ⟶α≤β→γ<β (inj₁ γ⟶α<β) = trans [ <l ] γ⟶α<β 
γ⟶α≤β→γ<β (inj₂ refl) = [ <l ]

γ⟶α≤β→α<β : ∀ {γ α β} → (γ ⟶ α) ≤ β → α < β
γ⟶α≤β→α<β (inj₁ γ⟶α<β) =  trans [ <r ] γ⟶α<β
γ⟶α≤β→α<β (inj₂ refl) = [ <r ]
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

NeαComp : {x : V} → αCompatiblePred (Ne x)
NfαComp : αCompatiblePred Nf

NeαComp {.x} ∼αv            (v x)       = v x
NeαComp {x} (∼α· M~M' N~N') (NeM · NfN) = NeαComp M~M' NeM · NfαComp N~N' NfN

NfαComp M~N               (ne NeM) = ne (NeαComp M~N NeM)
NfαComp (∼αƛ xs xzM~yzN)  (ƛ NfM)  = {!!}

infix 4 _↓
infix 5 _↓_

_↓_ : Λ → Λ → Set
M ↓ N = M →α* N × Nf N 

_↓ : Λ → Set
M ↓ = ∃ (λ N → M ↓ N)

↓αComp : αCompatiblePred (_↓)
↓αComp M~M' (N ∶ M→N ∶ nfN) = N ∶ trans (just (inj₂ (σ M~M'))) M→N ∶ nfN

ƛ↓ : {x : Atom}{M : Λ} → M ↓ → ƛ x M ↓
ƛ↓ {x} {M} (N ∶ M→N ∶ nfN) = ƛ x N ∶ abs-star M→N ∶ ƛ nfN

·l↓ : {M M' N : Λ} → M ∼α M'  → M · N ↓ →  M' · N ↓
·l↓ M~M' (P ∶ MN→P ∶ nfP) = P ∶ trans (app-star-l (just (inj₂ (σ M~M')))) MN→P ∶ nfP

data WNe : V → Λ → Set where
  wv : (x : V) → WNe x (v x)
  w· : {M N : Λ}{x : V} → WNe x M → WNe x (M · N)

WNe⊂Ne : {x : V}{M : Λ} → Ne x M → WNe x M
WNe⊂Ne (v x)       = wv x
WNe⊂Ne (WNexM · _) = w· (WNe⊂Ne WNexM)

Nf∧Wne⊂Ne : {x : V}{M : Λ} → Nf M → WNe x M → Ne x M
Nf∧Wne⊂Ne (ne (v .x))       (wv x)     = v x
Nf∧Wne⊂Ne (ne (NexM · nfN)) (w· WNexM) = Nf∧Wne⊂Ne (ne NexM) WNexM · nfN
Nf∧Wne⊂Ne (ƛ nf)            () 
\end{code}

\begin{code}
lemmaM⟶N∧N↓⟶M↓ : {M N : Λ} → M →α* N → N ↓ → M ↓
lemmaM⟶N∧N↓⟶M↓ M⟶N (P ∶ N⟶P ∶ nfP) = P ∶ trans M⟶N N⟶P ∶ nfP

lemmav↓ : {x : V}{N : Λ} → (v x) →α* N → N ≡ v x
lemmav↓ refl = refl
lemmav↓ (just (inj₁ (ctxinj ())))
lemmav↓ (just (inj₂ ∼αv)) = refl
lemmav↓ {x} {N} (trans {b = P} x→P P→N)
  with P | lemmav↓ x→P
... | .(v x) | refl = lemmav↓ P→N

lemmaWNeƛ : {x : V}{M : Λ} → WNe x M → ¬ ∃₂ (λ y N → M ≡ ƛ y N)
lemmaWNeƛ (wv x) (_ ∶ _ ∶ ()) 
lemmaWNeƛ (w· w) (_ ∶ _ ∶ ())

lemma1 : {x : V}{M N : Λ} → WNe x M → M →α* N → WNe x N
lemma1 {.x} {.(v x)} {N} (wv x) x→N
  with N | lemmav↓ x→N
... | .(v x) | refl = wv x
lemma1 {x} {M · P}        .{M · P}   WNexMP     refl =  WNexMP
lemma1 {x} {(ƛ y M)  · P} {N}        (w· WNexM) (just (inj₁ (ctxinj (▹β .{M} {Q} .{y})))) = ⊥-elim ((lemmaWNeƛ WNexM) (y ∶ M ∶ refl))
lemma1 {x} {(v y)    · P} {N}        (w· _)     (just (inj₁ (ctxinj ()))) 
lemma1 {x} {(M · M') · P} {N}        (w· _)     (just (inj₁ (ctxinj ()))) 
lemma1 {x} {M · P}        .{M' · P}  (w· WNexM) (just (inj₁ (ctx·l {t₁' = M'} M→M'))) = w· (lemma1 {x} {M} {M'} WNexM (just (inj₁ M→M')))
lemma1 {x} {M · P}        .{M · P'}  (w· WNexM) (just (inj₁ (ctx·r {t₂' = P'} P→P'))) = w· WNexM
lemma1 {x} {M · P}        .{M' · N'} (w· WNexM) (just (inj₂ (∼α· {M' = M'} {N' = N'} M~M' N~N'))) = w· (lemma1 {x} {M} {M'} WNexM (just (inj₂ M~M')))
lemma1 {x} {M · P}        {N}        (w· WNexM) (trans {b = Q} MP→Q Q→N) = lemma1 {x} (lemma1 {x} {M · P}  (w· WNexM) MP→Q) Q→N

corollary1 : {x : V}{M N : Λ} → WNe x M → M ↓ N → WNe x N
corollary1 WNexM (M→N ∶ _) = lemma1 WNexM M→N
\end{code}

\begin{code}
lemma2 : {x : V}{α β : Type}{M N : Λ}{Γ : Cxt}
   → WNe x M → Γ ⊢ M ∶ α ⟶ β → Γ ⊢ N ∶ α 
  → Σₓ (x ∈ Γ) (λ x∈Γ → α ⟶ β ≤ Γ ⟨ x∈Γ ⟩ × (α < Γ ⟨ x∈Γ ⟩))
lemma2 .{x} {α} {β} .{v x} {N} (wv x) Γ⊢x:α→β  Γ⊢N:α =
    proj₁ (lemma⊢v Γ⊢x:α→β)
  ∶ subst (λ e → α ⟶ β ≤ e) (sym (proj₂ (lemma⊢v Γ⊢x:α→β))) (inj₂ refl)
  ∶ subst (λ e → α < e) (sym (proj₂ (lemma⊢v Γ⊢x:α→β))) [ <l ]
lemma2 {x} {α} {β} {M · P} {N} (w· NexM) (⊢· {γ} Γ⊢M∶γ⟶α⟶β Γ⊢P:γ) Γ⊢N∶α
  with lemma2 {x} {γ} {α ⟶ β} NexM Γ⊢M∶γ⟶α⟶β Γ⊢P:γ  
... | x∈Γ ∶ γ⟶α⟶β≤Γx ∶ γ<Γx =
    x∈Γ
  ∶ inj₁ (γ⟶α≤β→α<β γ⟶α⟶β≤Γx)
  ∶ γ⟶α≤β→γ<β (inj₁ (γ⟶α≤β→α<β γ⟶α⟶β≤Γx)) 
\end{code}

\begin{code}
lemma3 : {x y : V}{M N : Λ} → x ≢ y → WNe y M → WNe y (M [ x ≔ N ])
lemma3 {x} .{y} .{v y} {N} x≢y (wv y)
  with v y [ x ≔ N ] | lemmahvar≢ {x} {y} {N} x≢y
... | .(v y) | refl = wv y  
lemma3 {x} {y} {M · P} {N} x≢y (w· WNeyM) = w· (lemma3 x≢y WNeyM)
\end{code}

\begin{code}
thm-lemma1 : {β : Type}{x : Atom}{N : Λ} → Λ → Set
thm-lemma1 {β} {x} {N} M = {α : Type}{Γ : Cxt} → Γ ‚ x ∶ β  ⊢ M ∶ α →  Γ ⊢ N ∶ β  → Nf M → N ↓ → M [ x ≔ N ] ↓

thm-lemma1-αComp : {β : Type}{x : Atom}{N : Λ} → αCompatiblePred (thm-lemma1 {β} {x} {N})
thm-lemma1-αComp {β} {x} {N} {M} {M'} M~M' lemma1M {α} {Γ} Γ‚x∶β⊢M'∶α Γ⊢N∶β nfM' N↓
  with M' [ x ≔ N ]   | lemmaSubst1 N x M~M'
... | .(M [ x ≔ N ])  | refl = lemma1M (lemma⊢α Γ‚x∶β⊢M'∶α (σ M~M')) Γ⊢N∶β (NfαComp (σ M~M') nfM') N↓   

thm-lemma2 : {β : Type}{x : Atom}{N : Λ} → Λ → Set
thm-lemma2 {β} {x} {N} M =
       {α : Type}{Γ : Cxt}
       → Γ ⊢ M ∶ β ⟶ α
       → Γ ⊢ N ∶ β
       → Nf M  
       → N ↓  
       → M · N ↓

thm-lemma2-αComp : {β : Type}{x : Atom}{N : Λ} → αCompatiblePred (thm-lemma2 {β} {x} {N})
thm-lemma2-αComp {β} {x} {N} {M} {M'} M~M' lemma2M Γ⊢M'∶β→α Γ⊢N∶β nfM' N↓ 
  = ·l↓ M~M' (lemma2M (lemma⊢α Γ⊢M'∶β→α (σ M~M')) Γ⊢N∶β (NfαComp (σ M~M') nfM') N↓) 

thm : {β : Type}{x : Atom}{N : Λ} → Λ → Set
thm {β} {x} {N} M = thm-lemma1 {β} {x} {N} M × thm-lemma2 {β} {x} {N} M 

thm-αComp : {β : Type}{x : Atom}{N : Λ} → αCompatiblePred (thm {β} {x} {N}) 
thm-αComp {β} {x} {N} M~M' (lemma1M ∶ lemma2M) = thm-lemma1-αComp {β} {x} {N} M~M' lemma1M ∶ thm-lemma2-αComp {β} {x} {N} M~M' lemma2M
\end{code}

\begin{code}
lemma1-var : {x  y : Atom}{N : Λ} → N ↓ → (v y) [ x ≔ N ] ↓
lemma1-var {x} {y} {N} N↓ with (v y) [ x ≔ N ] | lemmahvar {x} {y} {N}
... | .N     | inj₁ (x≡y ∶ refl) = N↓
... | .(v y) | inj₂ (x≢y ∶ refl) = v y ∶ refl ∶ ne (v y)
\end{code}

\begin{code}
thm-subst : {x : Atom}{M N : Λ} → M  [ x ≔ N ] ↓ → (ƛ x M) · N ↓
thm-subst (P ∶ M[x≔N]→P ∶ nfP) =  P ∶ trans β-star M[x≔N]→P ∶ nfP
\end{code}

Induction on type β, and inside it a term α-induction on M

\begin{code}
thm-proof : {β : Type}{x : Atom}{N : Λ}{M : Λ} → Acc< β → thm {β} {x} {N} M
thm-proof {τ}      {x} {N} {M} _          = {!!}
thm-proof {β ⟶ β'} {x} {N} {M} (acc accβ) =
  TermαPrimInd2 (thm {β ⟶ β'} {x} {N}) (x ∷ fv N) (thm-αComp {β ⟶ β'} {x} {N}) {!!} thm-app {!!} M -- thm-var thm-app thm-abs
  where
  lemma1-app : (M Q : Λ) → thm {β ⟶ β'} {x} {N} M → thm {β ⟶ β'} {x} {N} Q
          → ((z : Atom) → z ∈l x ∷ fv N → z ∉b M · Q)
          → thm-lemma1 {β ⟶ β'} {x} {N} (M · Q)
  lemma1-app M Q thmM thmQ fresh (⊢· Γ,x:β→β'⊢M:γ→α Γ,x:β→β'⊢Q:γ) Γ⊢N:β→β' (ne {y} (NeyM · NfQ)) N↓
    with x ≟ₐ y 
  ... | no x≢y  with (proj₁ thmM) Γ,x:β→β'⊢M:γ→α Γ⊢N:β→β' (ne NeyM) N↓
                   | (proj₁ thmQ) Γ,x:β→β'⊢Q:γ Γ⊢N:β→β' NfQ N↓
                   | lemma3 {x} {y} {M} {N} x≢y (WNe⊂Ne NeyM)
  ... | R ∶ M[x≔N]→R ∶ NfR
      | S ∶ Q[x≔N]→S ∶ NfS
      | WNeyM[x≔N]
      =  R · S
      ∶  app-star M[x≔N]→R Q[x≔N]→S
      ∶  ne (Nf∧Wne⊂Ne NfR (corollary1 {y} WNeyM[x≔N] (M[x≔N]→R ∶ NfR)) · NfS)
  lemma1-app M Q thmM thmQ fresh {α} {Γ} (⊢· {γ} Γ,x:β→β'⊢M:γ→α Γ,x:β→β'⊢Q:γ) Γ⊢N:β→β' (ne {x} (NexM · NfQ)) N↓  
      | yes refl = lemmaM⟶N∧N↓⟶M↓ (app-star-l M[x≔N]⟶R) RQ[x≔N]↓ 
    where
    -- subordinate induction
    hiP : M [ x ≔ N ] ↓
    hiP = (proj₁ thmM) Γ,x:β→β'⊢M:γ→α Γ⊢N:β→β' (ne NexM) N↓
    R : Λ
    R = proj₁ hiP
    M[x≔N]⟶R : M [ x ≔ N ] →α* R
    M[x≔N]⟶R = proj₁ (proj₂ hiP)
    NfR : Nf R
    NfR = proj₂ (proj₂ hiP)
    -- subordinate induction    
    hiQ : Q [ x ≔ N ] ↓
    hiQ = (proj₁ thmQ) Γ,x:β→β'⊢Q:γ Γ⊢N:β→β' NfQ N↓
    γ<β→β' : γ < β ⟶ β'
    γ<β→β' with lemma2 (WNe⊂Ne NexM) Γ,x:β→β'⊢M:γ→α Γ,x:β→β'⊢Q:γ
    ... | here refl ∶ γ→α≤β→β' ∶ γ<β→β = γ<β→β 
    ... | there x≢x _ ∶ _ ∶ _ =  ⊥-elim (x≢x refl)
    Γ⊢R:γ⟶α : Γ ⊢ R ∶ γ ⟶ α
    Γ⊢R:γ⟶α = lemma⊢→α* (lemma⊢[] Γ,x:β→β'⊢M:γ→α Γ⊢N:β→β') M[x≔N]⟶R 
    Γ⊢Q[x≔N]:γ : Γ ⊢ Q [ x ≔ N ] ∶ γ
    Γ⊢Q[x≔N]:γ = lemma⊢[] Γ,x:β→β'⊢Q:γ Γ⊢N:β→β'
    -- main induction on β type
    RQ[x≔N]↓ : R · (Q [ x ≔ N ]) ↓
    RQ[x≔N]↓ = (proj₂ (thm-proof {γ} {x} {Q [ x ≔ N ]} {R} (accβ γ γ<β→β'))) Γ⊢R:γ⟶α Γ⊢Q[x≔N]:γ NfR hiQ 

  lemma2-app : (M Q : Λ) → thm {β ⟶ β'} {x} {N} M → thm {β ⟶ β'} {x} {N} Q
          → ((z : Atom) → z ∈l x ∷ fv N → z ∉b M · Q)
          → thm-lemma2 {β ⟶ β'} {x} {N} (M · Q)
  lemma2-app M Q thmM thmQ fresh Γ,x:β→β'⊢MQ:α Γ⊢N:β→β' (ne {y} NeyMQ) (N' ∶ N→N' ∶ NfN') =
      (M · Q) · N'
    ∶ app-star-r N→N'
    ∶ ne (NeyMQ · NfN')                    
  thm-app : (M Q : Λ) → thm {β ⟶ β'} {x} {N} M → thm {β ⟶ β'} {x} {N} Q
          → ((z : Atom) → z ∈l x ∷ fv N → z ∉b M · Q)
          → thm {β ⟶ β'} {x} {N} (M · Q)
  thm-app M Q thmM thmQ fresh = lemma1-app M Q thmM thmQ fresh ∶ lemma2-app M Q thmM thmQ fresh 


--   -- where
--   -- thm-var-lemma1 : (y : Atom) → lemma1 {x} {γ ⟶ φ} {β} {Γ} {N} (v y)
--   -- thm-var-lemma1 y Γ,x:β⊢y:γ→φ Γ⊢N:β N↓ = lemma1-var {x} {y} N↓ 
--   -- thm-var-lemma2 : (y : Atom) → lemma2 {x} {γ ⟶ φ} {β} {Γ} {N} (v y)
--   -- thm-var-lemma2 y Γ,x:β⊢y:γ→φ Γ⊢N:β N↓ _     {P}      (y[x≔N]→P ∶ ne neP) {Q}  Γ⊢Q:γ (R ∶ Q→R ∶ nfR)
--   --   = P · R ∶ app-star-r Q→R ∶ ne (neP · nfR)
--   -- thm-var-lemma2 y Γ,x:β⊢y:γ→φ Γ⊢N:β N↓ refl  {ƛ z P}  (y[x≔N]→ƛzP ∶ ƛ nfP) {Q}  Γ⊢Q:γ Q↓
--   --   with lemma⊢→α* (lemma⊢[] Γ,x:β⊢y:γ→φ Γ⊢N:β) y[x≔N]→ƛzP
--   -- ... | ⊢ƛ Γ,z:γ⊢P:φ = thm-subst (proj₁ (thm-proof {z} {φ} P) Γ,z:γ⊢P:φ Γ⊢Q:γ Q↓)
--   -- thm-var : (y : Atom) → thm {x} {γ ⟶ φ} {β} {Γ} {N} (v y)
--   -- thm-var y = thm-var-lemma1 y ∶ thm-var-lemma2 y

--   -- thm-abs : (M : Λ)(z : Atom) → thm {x} {γ ⟶ φ} {β} {Γ} {N} M
--   --         → ((w : Atom) → w ∈l x ∷ fv N ++ dom Γ → w ∉b ƛ z M)
--   --         → thm {x} {γ ⟶ φ} {β} {Γ} {N} (ƛ z M)
--   -- thm-abs M z (lemma1M ∶ lemma2M) fresh = {!!}

  
\end{code}


