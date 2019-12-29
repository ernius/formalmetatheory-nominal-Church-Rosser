\begin{code}
module Types where

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

infix 1 _⊢_∶_
infix 4 （_∙_）ₗ_ 
\end{code}

\begin{code}
data Type : Set where
  τ    : Type
  _⟶_  : Type → Type → Type
import Context
open module M = Context (Type)(_≟_) public renaming (begin_ to begin⊆_;_∎ to _∎⊆;_∼⟨_⟩_ to _⊆⟨_⟩_)
\end{code}

\begin{code}
（_∙_）ₗ_  : Atom → Atom → Cxt → Cxt
（ a ∙ b ）ₗ Γ = map (mapₓ (λ c → （ a ∙ b ）ₐ c) id) Γ

lemma（）ₗcomm : {a b : Atom}{Γ : Cxt} → (（ a ∙ b ）ₗ Γ) ≡ (（ b ∙ a ）ₗ Γ)
lemma（）ₗcomm {Γ = []}           = refl
lemma（）ₗcomm {Γ = (c ∶ α) ∷ Γ}  = cong₂ _∷_ (cong₂ _∶_  (lemma∙ₐcomm {c = c}) refl) lemma（）ₗcomm

lemma（）ₗidem : {a b : Atom}{Γ : Cxt} → Γ ≡ (（ a ∙ b ）ₗ (（ a ∙ b ）ₗ Γ))
lemma（）ₗidem          {Γ = []}           = refl
lemma（）ₗidem {a} {b}  {Γ = (c ∶ α) ∷ Γ}  = cong₂ _∷_ (cong₂ _∶_  (sym (lemma（ab）（ab）c≡c {a} {b} {c})) refl) lemma（）ₗidem

lemma∈（） :  {a b x : Atom}{Γ : Cxt}
             → (x∈Γ : x ∈ Γ) 
             → Σₓ (（ a ∙ b ）ₐ x ∈ （ a ∙ b ）ₗ Γ) (λ （ab）x∈（ab）Γ → Γ ⟨ x∈Γ ⟩ ≡ (（ a ∙ b ）ₗ Γ) ⟨ （ab）x∈（ab）Γ ⟩) 
lemma∈（） (here refl)      = here refl ∶ refl
lemma∈（） (there ¬px x∈Γ)  = mapₓ (there (lemma∙ₐinj ¬px)) id (lemma∈（） x∈Γ)

lemma（）∈ :  {a b x : Atom}{Γ : Cxt}
             → (x∈（ab）Γ : x ∈ （ a ∙ b ）ₗ Γ) →
             (x ≡ b          × Σₓ (a ∈ Γ) (λ a∈Γ  → (（ a ∙ b ）ₗ Γ) ⟨ x∈（ab）Γ ⟩ ≡ Γ ⟨ a∈Γ ⟩))  ∨ 
             (x ≡ a × b ≢ a  × Σₓ (b ∈ Γ) (λ b∈Γ  → (（ a ∙ b ）ₗ Γ) ⟨ x∈（ab）Γ ⟩ ≡ Γ ⟨ b∈Γ ⟩))  ∨ 
             (x ≢ a × x ≢ b  × Σₓ (x ∈ Γ) (λ x∈Γ  → (（ a ∙ b ）ₗ Γ) ⟨ x∈（ab）Γ ⟩ ≡ Γ ⟨ x∈Γ ⟩))
lemma（）∈ {a} {b} {x} {[]}            () 
lemma（）∈ {a} {b} {x} {(c ∶ α) ∷ Γ}   (here x≡（ab）c)
  with lemma∙ₐ a b c
lemma（）∈ {a} {b} {x} {(.a ∶ α) ∷ Γ}  (here x≡（ab）c)
  | inj₁ (refl ∶ （ab）c≡b )               
  = inj₁ ((trans≡ x≡（ab）c （ab）c≡b) ∶ here refl ∶ refl)
lemma（）∈ {a} {b} {x} {(.b ∶ α) ∷ Γ}  (here x≡（ab）c)
  | inj₂ (inj₁ (refl ∶ b≢a ∶ （ab）c≡a ))  
  = inj₂ (inj₁ ((trans≡ x≡（ab）c （ab）c≡a) ∶ b≢a ∶ here refl ∶ refl ))
lemma（）∈ {a} {b} {x} {(c ∶ α) ∷ Γ}   (here x≡（ab）c) 
  | inj₂ (inj₂ (c≢a ∶ c≢b ∶ （ab）c≡c )) with （ a ∙ b ）ₐ c | （ab）c≡c
lemma（）∈ {a} {b} {x} {(.x ∶ α) ∷ Γ}   (here refl)  
  | inj₂ (inj₂ (x≢a ∶ x≢b ∶ （ab）c≡c )) | .x | refl
  = inj₂ (inj₂ (x≢a ∶ x≢b ∶ here refl ∶ refl)) 
lemma（）∈ {a} {b} {x} {(c ∶ α) ∷ Γ}   (there x≢（ab）c x∈（ab）Γ) 
  = map+  (mapₓ id (λ {x≡b} → mapₓ (there (λ a≡c → ⊥-elim (x≢（ab）c (trans≡ x≡b (sym (lemma∙ₐc≡a a b c (sym a≡c))))) )) id)) 
          (map+  (mapₓ id (λ {x≡a} → mapₓ id (λ {b≢a} → mapₓ (there (λ b≡c → ⊥-elim (x≢（ab）c (trans≡ x≡a (sym (lemma∙ₐc≡b a b c (sym b≡c))))))) id))) 
                 (mapₓ id (λ {x≢b} → mapₓ id (λ {x≢a} → mapₓ (there (λ x≡c → ⊥-elim (x≢（ab）c (trans≡ x≡c (sym (lemma∙ₐc≢a∧c≢b (a≢b∧a≡c→c≢b x≢b x≡c) (a≢b∧a≡c→c≢b x≢a x≡c)))))))id)))) 
          (lemma（）∈ {a} {b} {x} {Γ} x∈（ab）Γ)

lemma（）⊆ : {x y : Atom}{α : Type}{Γ : Cxt} → y ∉l dom Γ → (（ x ∙ y ）ₗ Γ) ‚ y ∶ α ⊆ Γ ‚ y ∶ α
lemma（）⊆ {x} {y} y∉Γ .{y} (here  refl)          = here refl ∶ refl
lemma（）⊆ {x} {y} y∉Γ {z}  (there z≢y z∈（xy）Γ) 
  with lemma（）∈ z∈（xy）Γ
lemma（）⊆ {x} {y} y∉Γ .{y}  (there y≢y y∈（xy）Γ) 
  | inj₁ (refl ∶ _)                                             = ⊥-elim (y≢y refl)
lemma（）⊆ {x} {y} y∉Γ .{x}  (there x≢y x∈（xy）Γ) 
  | inj₂ (inj₁ (refl ∶ y≢x ∶ y∈Γ ∶ （xy）Γ⟨x∈（xy）Γ⟩≡Γ⟨y∈Γ⟩ ))  = ⊥-elim (y∉Γ (corollary-lemma∈→∈[] y∈Γ))
lemma（）⊆ {x} {y} y∉Γ {z}  (there z≢y z∈（xy）Γ) 
  | inj₂ (inj₂ (z≢x ∶ _ ∶ z∈Γ ∶ （xy）Γ⟨z∈（xy）Γ⟩≡Γ⟨z∈Γ⟩))      = there z≢y z∈Γ ∶ （xy）Γ⟨z∈（xy）Γ⟩≡Γ⟨z∈Γ⟩
\end{code}

%<*type>
\begin{code}
data _⊢_∶_ (Γ : Cxt): Λ → Type → Set where
  ⊢v : {x : V}                     → (p∈ : x ∈ Γ)                → Γ ⊢ v x ∶ Γ ⟨ p∈ ⟩
  ⊢· : {α β : Type}{M N : Λ}       → Γ ⊢ M ∶ α ⟶ β → Γ ⊢ N ∶ α   → Γ ⊢ M · N ∶ β
  ⊢ƛ : {x : V}{α β : Type}{M : Λ}  → Γ ‚ x ∶ α ⊢ M ∶ β           → Γ ⊢ ƛ x M ∶ α ⟶ β
\end{code}
%</type>


\begin{code}
lemma⊢v : {x : V}{α : Type}{Γ : Cxt} → Γ ⊢ v x ∶ α → Σₓ (x ∈ Γ) (λ x∈Γ → Γ ⟨ x∈Γ ⟩ ≡ α)
lemma⊢v (⊢v x∈Γ) = x∈Γ ∶ refl
\end{code}

Some type results:

%<*weakening>
\begin{code}
lemmaWeakening⊢ :  {Γ Δ : Cxt}{M : Λ}{α : Type}
                →  Γ ⊆ Δ → Γ ⊢ M ∶ α → Δ ⊢ M ∶ α
\end{code}
%</weakening>

\begin{code}
lemmaWeakening⊢ Γ⊆Δ (⊢v x∈Γ) rewrite proj₂ (Γ⊆Δ x∈Γ) 
  = ⊢v (proj₁ (Γ⊆Δ x∈Γ))
lemmaWeakening⊢ Γ⊆Δ (⊢· Γ⊢M:α⟶β Γ⊢N:α) 
  = ⊢· (lemmaWeakening⊢ Γ⊆Δ Γ⊢M:α⟶β) (lemmaWeakening⊢ Γ⊆Δ Γ⊢N:α)
lemmaWeakening⊢ Γ⊆Δ (⊢ƛ Γ,y:α⊢M:β) 
  = ⊢ƛ (lemmaWeakening⊢ (lemma⊆∷ Γ⊆Δ) Γ,y:α⊢M:β)
\end{code}

\begin{code}
lemmaWeakening⊢# :  {Γ : Cxt}{x : Atom}{M : Λ}{α β : Type}
                    →  x # M 
                    → Γ ⊢ M ∶ α 
                    → Γ ‚ x ∶ β ⊢ M ∶ α
lemmaWeakening⊢# {Γ}      (#v y≢x)       (⊢v y∈Γ)    
  = ⊢v (there y≢x y∈Γ)
lemmaWeakening⊢# {Γ}      (#· x#M x#M')  (⊢· Γ⊢M∶α→β Γ⊢M'∶α) 
  = ⊢· (lemmaWeakening⊢# x#M Γ⊢M∶α→β) (lemmaWeakening⊢# x#M' Γ⊢M'∶α)
lemmaWeakening⊢# {Γ} {x}  x#ƛyM          (⊢ƛ {y} Γ,y:α⊢M∶β) 
  with x ≟ₐ y 
lemmaWeakening⊢#          x#ƛyM          (⊢ƛ {y} Γ,y:α⊢M∶β) 
    | yes refl  = ⊢ƛ (lemmaWeakening⊢ lemma⊆x Γ,y:α⊢M∶β)
lemmaWeakening⊢# {Γ} {x}  x#ƛyM          (⊢ƛ {y} Γ,y:α⊢M∶β) 
    | no  x≢y   = ⊢ƛ (lemmaWeakening⊢ (lemma⊆xy (sym≢ x≢y)) (lemmaWeakening⊢# (lemma#λ x≢y x#ƛyM) Γ,y:α⊢M∶β))
\end{code}

%<*typeweakening#>
\begin{code}
lemmaStrengthening⊢#  : {Γ : Cxt}{M : Λ}{x : V}{α β : Type} 
                      → x # M → Γ ‚ x ∶ β ⊢ M ∶ α → Γ ⊢ M ∶ α
lemmaStrengthening⊢# (#v x≢x)      (⊢v (here refl))      = ⊥-elim (x≢x refl)
lemmaStrengthening⊢# x#M           (⊢v (there y≢x y∈Γ))  = ⊢v y∈Γ
lemmaStrengthening⊢# (#· x#M x#N)  (⊢· Γ,x∶β⊢M∶α'⟶β' Γ,x:β⊢N∶α') 
  = ⊢·  (lemmaStrengthening⊢# x#M Γ,x∶β⊢M∶α'⟶β') 
        (lemmaStrengthening⊢# x#N Γ,x:β⊢N∶α')
lemmaStrengthening⊢# {M = ƛ y M}  {x} 
                     x#ƛyM         (⊢ƛ Γ,x:β,y:α'⊢M∶β') 
  with x ≟ y
lemmaStrengthening⊢# {M = ƛ .x M}  {x} 
                     x#ƛxM         (⊢ƛ Γ,x:β,x:α'⊢M∶β') 
  | yes refl 
  = ⊢ƛ (lemmaWeakening⊢ lemma⊆xx Γ,x:β,x:α'⊢M∶β')
lemmaStrengthening⊢# {M = ƛ .x M} {x} 
                     #ƛ≡           (⊢ƛ Γ,x:β,x:α'⊢M∶β') 
  | no x≢x   
  = ⊥-elim (x≢x refl)
lemmaStrengthening⊢# {M = ƛ y M} {x} 
                     (#ƛ x#M)      (⊢ƛ Γ,x:β,y:α'⊢M∶β') 
  | no x≢y   
  = ⊢ƛ (lemmaStrengthening⊢# x#M (lemmaWeakening⊢ (lemma⊆xy x≢y) Γ,x:β,y:α'⊢M∶β'))
\end{code}
%</typeweakening#>

%<*typeequiv>
\begin{code}
lemma⊢Equiv  :  {x y : Atom}{Γ : Cxt}{M : Λ}{α : Type}
             →  Γ ⊢ M ∶ α → （ x ∙ y ）ₗ Γ ⊢ （ x ∙ y ） M ∶ α
lemma⊢Equiv {x} {y} (⊢v z∈Γ)            
  with lemma∈（） {x} {y} z∈Γ
... | （xy）z∈（xy）Γ ∶ Γ⟨z∈Γ⟩≡（xy）Γ⟨（xy）z∈（xy）Γ⟩ 
  rewrite Γ⟨z∈Γ⟩≡（xy）Γ⟨（xy）z∈（xy）Γ⟩ = ⊢v （xy）z∈（xy）Γ
lemma⊢Equiv (⊢· Γ⊢M∶α→β Γ⊢M:α)  = ⊢· (lemma⊢Equiv Γ⊢M∶α→β) (lemma⊢Equiv Γ⊢M:α)
lemma⊢Equiv (⊢ƛ Γ,x:α⊢M:β)      = ⊢ƛ (lemma⊢Equiv Γ,x:α⊢M:β)
\end{code}
%</typeequiv>

%<*typealpha>
\begin{code}
P⊢α : (M : Λ) → Set
P⊢α M = {Γ : Cxt}{α : Type}{N : Λ} → Γ ⊢ M ∶ α → M ∼α N → Γ ⊢ N ∶ α

lemma⊢α : {M : Λ} → P⊢α M
lemma⊢α {M} 
  = TermIndPerm  P⊢α 
                 lemmav
                 lemma· 
                 lemmaƛ 
                 M         
  where
  lemmav : (a : ℕ) → P⊢α (v a)
  lemmav a (⊢v a∈Γ) ∼αv = ⊢v a∈Γ
  lemma· : (M N : Λ) → P⊢α M → P⊢α N → P⊢α (M · N)
  lemma· M N PM PN (⊢· Γ⊢M:α→β Γ⊢N∶α) (∼α· M~M' N~N') 
    = ⊢· (PM Γ⊢M:α→β M~M') (PN Γ⊢N∶α N~N')
  lemmaƛ :  (M : Λ) (b : ℕ) 
            → ((π : List (Atom × Atom)) → P⊢α (π ∙ M)) 
            → P⊢α (ƛ b M)
  lemmaƛ M x PMπ {Γ} {α ⟶ β} {ƛ y N} (⊢ƛ .{x} .{α} .{β} Γ,x:α⊢M:β) (∼αƛ xs ∀z∉xs,（xz）M∼（yz）N) 
    = ⊢ƛ weakening2
    where
    z = χ' (y ∷ (xs ++ dom Γ ++ fv N))
    z∉y∷xs++domΓ++fvN : z ∉l y ∷ (xs ++ dom Γ ++ fv N)
    z∉y∷xs++domΓ++fvN  = lemmaχ∉ (y ∷ (xs ++ dom Γ ++ fv N))
    z∉xs++domΓ++fvN : z ∉l xs ++ dom Γ ++ fv N
    z∉xs++domΓ++fvN  = b∉a∷xs→b∉xs z∉y∷xs++domΓ++fvN
    z∉domΓ : z ∉l dom Γ
    z∉domΓ = c∉xs++ys→c∉xs (c∉xs++ys→c∉ys {xs = xs} z∉xs++domΓ++fvN)
    z≢y : z ≢ y
    z≢y = b∉a∷xs→b≢a z∉y∷xs++domΓ++fvN
    z#N : z # N
    z#N = lemma∉fv→# (c∉xs++ys→c∉ys {xs = dom Γ} (c∉xs++ys→c∉ys {xs = xs} z∉xs++domΓ++fvN))
    （xz）Γ,z:α⊢（xz）M:β : （ x ∙ z ）ₗ Γ ‚ z ∶ α ⊢ （ x ∙ z ） M ∶ β
    （xz）Γ,z:α⊢（xz）M:β = subst  (λ H → （ x ∙ z ）ₗ Γ ‚ H ∶ α ⊢ （ x ∙ z ） M ∶ β)
                                  (lemma∙ₐ（ab）a≡b {x} {z})
                                  (lemma⊢Equiv {x} {z} Γ,x:α⊢M:β)
    weakening : Γ ‚ z ∶ α ⊢ （ x ∙ z ） M ∶ β
    weakening = lemmaWeakening⊢ (lemma（）⊆ z∉domΓ) （xz）Γ,z:α⊢（xz）M:β
    hi : Γ ‚ z ∶ α ⊢ （ y ∙ z ） N ∶ β
    hi = PMπ [(x ∶ z)] weakening (∀z∉xs,（xz）M∼（yz）N z (c∉xs++ys→c∉xs z∉xs++domΓ++fvN))
    equivhi : （ y ∙ z ）ₗ Γ ‚ y ∶ α ⊢ N ∶ β
    equivhi = subst₂ (λ P Q → （ y ∙ z ）ₗ Γ ‚ P ∶ α ⊢ Q ∶ β) (lemma∙ₐ（ab）b≡a {y} {z}) lemma（ab）（ab）M≡M (lemma⊢Equiv {y} {z} hi)
    lemma⊂ : （ y ∙ z ）ₗ Γ ‚ y ∶ α ‚ z ∶ α ⊆ Γ ‚ y ∶ α ‚ z ∶ α
    lemma⊂ = begin⊆
               （ y ∙ z ）ₗ Γ ‚ y ∶ α ‚ z ∶ α
             ⊆⟨ lemma⊆xy (sym≢ z≢y) ⟩
               （ y ∙ z ）ₗ Γ ‚ z ∶ α ‚ y ∶ α
             ⊆⟨  lemma⊆∷ (lemma（）⊆ z∉domΓ) ⟩
                Γ ‚ z ∶ α ‚ y ∶ α
             ⊆⟨ lemma⊆xy z≢y ⟩
                Γ ‚ y ∶ α ‚ z ∶ α
             ∎⊆
    weakening2 : Γ ‚ y ∶ α ⊢ N ∶ β
    weakening2 = lemmaStrengthening⊢# z#N (lemmaWeakening⊢ lemma⊂ (lemmaWeakening⊢# z#N equivhi))
\end{code}
</typealpha>

Next we use alpha induction principle.

%<*typesusbstterm>
\begin{code}
P⊢[] : Atom → Λ → Λ → Set
P⊢[] x N M =  {Γ : Cxt}{α β : Type}
          → Γ ‚ x ∶ β ⊢ M ∶ α 
          → Γ ⊢ N ∶ β 
          → Γ ⊢ M [ x ≔ N ] ∶ α

αP⊢[] : {x : Atom}{N : Λ} → αCompatiblePred (P⊢[] x N)
αP⊢[] {x} {N} {P} {Q} P∼Q P⊢[]P {Γ} {α} Γ‚x∶β⊢Q∶α Γ⊢N∶β = subst (λ H → Γ ⊢ H ∶ α) (lemmaSubst1 N x P∼Q) (P⊢[]P (lemma⊢α Γ‚x∶β⊢Q∶α (σ P∼Q)) Γ⊢N∶β)

lemma⊢[]  : {x : Atom}{N : Λ}{M : Λ} → P⊢[] x N M 
lemma⊢[] {x} {N} {M} 
  = TermαPrimInd (P⊢[] x N) (αP⊢[] {x} {N}) lemmav lemma· (x ∷ fv N ∶ lemmaƛ) M
  where
  lemmav : (y : ℕ) → P⊢[] x N (v y)
  lemmav .x (⊢v (here refl))     Γ⊢N∶β 
    rewrite lemmahvar≡ {x} {N} 
    = Γ⊢N∶β
  lemmav y (⊢v (there y≢x y∈))  Γ⊢N∶β 
    rewrite lemmahvar≢ {x} {y} {N} (sym≢ y≢x)
    = ⊢v y∈ 
  lemma· : (P Q : Λ) → P⊢[] x N P → P⊢[] x N Q → P⊢[] x N (P · Q)
  lemma· P Q hiP hiQ (⊢· Γ⊢P∶α→γ Γ⊢Q∶α)  Γ⊢N∶β  
    = ⊢· (hiP Γ⊢P∶α→γ Γ⊢N∶β) (hiQ Γ⊢Q∶α Γ⊢N∶β)
  lemmaƛ : (P : Λ) (b : ℕ) → b ∉l x ∷ fv N → P⊢[] x N P → P⊢[] x N (ƛ b P)
  lemmaƛ P b b∉x∷fvN hiP (⊢ƛ Γ,x:β‚b∶α⊢P∶γ)  Γ⊢N∶β  
    = lemma⊢α (⊢ƛ (hiP (lemmaWeakening⊢ (lemma⊆xy x≢b) Γ,x:β‚b∶α⊢P∶γ) (lemmaWeakening⊢# b#N Γ⊢N∶β))) (σ (lemmaƛ∼[] P b∉x∷fvN)) 
    where
    b#N : b # N
    b#N = lemma∉fv→# (b∉x∷fvN ∘ there) 
    x≢b : x ≢ b
    x≢b = sym≢ (b∉a∷xs→b≢a b∉x∷fvN)
\end{code}
%</typesusbstterm>

\begin{code}
lemma⊢▹  :  {Γ : Cxt}{α : Type}{M N : Λ} 
         →  Γ ⊢ M ∶ α → M ▹ N → Γ ⊢ N ∶ α
lemma⊢▹ (⊢· (⊢ƛ Γ,x:α⊢M:β) Γ⊢N∶α) ▹β = lemma⊢[] Γ,x:α⊢M:β Γ⊢N∶α
\end{code}

\begin{code}
lemma⊢→β :  {Γ : Cxt}{α : Type}{M N : Λ} 
            → Γ ⊢ M ∶ α → M →β N → Γ ⊢ N ∶ α
lemma⊢→β Γ⊢M:α               (ctxinj  M▹N)    = lemma⊢▹ Γ⊢M:α M▹N
lemma⊢→β (⊢· Γ⊢M:α→β Γ⊢N:α)  (ctx·l   M→βM')  = ⊢· (lemma⊢→β Γ⊢M:α→β M→βM') Γ⊢N:α
lemma⊢→β (⊢· Γ⊢M:α→β Γ⊢N:α)  (ctx·r   N→βN')  = ⊢· Γ⊢M:α→β (lemma⊢→β Γ⊢N:α N→βN')
lemma⊢→β (⊢ƛ Γ,x:α⊢M:α)      (ctxƛ    M→βN)   = ⊢ƛ (lemma⊢→β Γ,x:α⊢M:α M→βN)
\end{code}

\begin{code}
lemma⊢→α :  {Γ : Cxt}{α : Type}{M N : Λ} 
            → Γ ⊢ M ∶ α → M →α N → Γ ⊢ N ∶ α
lemma⊢→α Γ⊢M:α (inj₁ M→βN)  = lemma⊢→β Γ⊢M:α M→βN
lemma⊢→α Γ⊢M:α (inj₂ M~N)   = lemma⊢α Γ⊢M:α M~N
\end{code}

\begin{code}
lemma⊢→α* :  {Γ : Cxt}{α : Type}{M N : Λ} 
             → Γ ⊢ M ∶ α → M →α* N → Γ ⊢ N ∶ α
lemma⊢→α* Γ⊢M:α refl                 = Γ⊢M:α
lemma⊢→α* Γ⊢M:α (just M→βN)          = lemma⊢→α Γ⊢M:α M→βN
lemma⊢→α* Γ⊢M:α (trans M→α*N N→α*P)  = lemma⊢→α* (lemma⊢→α* Γ⊢M:α M→α*N) N→α*P
\end{code}
