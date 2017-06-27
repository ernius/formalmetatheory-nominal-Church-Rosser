\begin{code}
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_ ; refl ; cong ; _≗_ ; sym ; trans ; inspect ;  setoid) renaming ([_] to [_]i)
open PropEq.≡-Reasoning

module Context {K : Set}(D : Set)(_≟_ : Decidable (_≡_ {A = K})) where

open import ListProperties

open import Data.Empty
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.List hiding (any;all)
open import Function
open import Data.List.Any as Any hiding (map;tail)
open import Data.List.Any.Membership
open Any.Membership-≡  renaming (_∈_ to _∈l_;_⊆_ to _⊆l_;_∉_ to _∉l_)
open import Data.Product renaming (map to map×)
open import Data.Sum hiding (map) renaming (_⊎_ to _∨_)
open import Data.Maybe hiding (Any;All;map;setoid) --(Any;All;setoid) --
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 
--private open module M   = Membership (PropEq.setoid K) using (_∈_) 
--private open module M≡  = Membership (PropEq.setoid (K × D)) renaming (_∈_ to _∈×_) 
infixl 3 _‚_ 
infix 2 _⊆_
infix 3 _∈_
\end{code}

\begin{code}
Cxt : Set
Cxt = List (K × D)

∅ : Cxt
∅ = []

dom : Cxt → List K
dom = map proj₁

_∈_ : K → Cxt → Set
x ∈ cxt = First (_≡_ x ∘ proj₁) cxt

-- _∈?_ : Decidable _∈_
-- k ∈? []        = no (λ ())
-- k ∈? (k' ∷ ks) with k ≟ k'
-- ... | yes k≡k' = yes (here k≡k')
-- ... | no  k≢k' with k ∈? ks
-- ...            | yes k∈ks 
--   = yes (there k∈ks)  
-- ...            | no  k∉ks 
--   = no (λ {  (here k≡k')   → ⊥-elim (k≢k' k≡k'); 
--              (there k∈ks)  → ⊥-elim (k∉ks k∈ks)})
_⟨_⟩ : {k : K} → (cxt : Cxt) → k ∈ cxt → D
[]             ⟨ ()            ⟩ 
((k , d) ∷ xs) ⟨ here  _       ⟩ = d
((k , d) ∷ xs) ⟨ there _ k∈xs  ⟩ = xs ⟨ k∈xs ⟩


lemma∈→∈[]  : {xs : Cxt}{x : K} → (p : x ∈ xs) → Σ D (λ d → ((x , d) ∈l xs) × (xs ⟨ p ⟩ ≡ d))
lemma∈→∈[] {(y , d) ∷ xs}  (here refl)       =  d , here refl , refl
lemma∈→∈[]                 (there x≢y x∈xs)  = map× id (map× there id) (lemma∈→∈[] x∈xs)

corollary-lemma∈→∈[] : {xs : Cxt}{x : K} → (p : x ∈ xs) → x ∈l dom xs
corollary-lemma∈→∈[] {(y , d) ∷ xs}  (here refl)       = here refl
corollary-lemma∈→∈[]                 (there x≢y x∈xs)  = there (corollary-lemma∈→∈[] x∈xs)

lemma∈[]→∈  : {xs : Cxt}{x : K}{d : D} → (p : (x , d) ∈l xs) → x ∈ xs
lemma∈[]→∈          (here refl)  =  here refl
lemma∈[]→∈ {x = x}  (there {y , d} p∈xs) with x ≟ y
... | yes  x≡y                   = here x≡y
... | no   x≢y                   = there x≢y (lemma∈[]→∈ p∈xs)

lemma∈!⟨⟩ : {xs : Cxt}{x : K} → (p p' : x ∈ xs) → xs ⟨ p ⟩ ≡ xs ⟨ p' ⟩
lemma∈!⟨⟩ (here  refl)        (here refl)        = refl
lemma∈!⟨⟩ (here  refl)        (there x≢y _)      = ⊥-elim (x≢y refl)
lemma∈!⟨⟩ (there x≢x x∈x∷xs)  (here refl)        = ⊥-elim (x≢x refl)
lemma∈!⟨⟩ (there x≢y x∈y∷xs)  (there _ x∈y∷xs')  = lemma∈!⟨⟩ x∈y∷xs x∈y∷xs'

_⊆_ : Cxt → Cxt → Set
Γ ⊆ Δ = {x : K}(x∈Γ : x ∈ Γ) → Σ (x ∈ Δ) (λ x∈Δ → Γ ⟨ x∈Γ ⟩ ≡ Δ ⟨ x∈Δ ⟩ )

ρ⊆ : Reflexive _⊆_
ρ⊆ x∈Γ = x∈Γ , refl

τ⊆ : Transitive _⊆_
τ⊆ Γ⊆Δ Δ⊆Ε x∈Γ with Γ⊆Δ x∈Γ
... | x∈Δ , Γ⟨x∈Γ⟩≡Δ⟨x∈Δ⟩ with Δ⊆Ε x∈Δ
... | x∈Ε , Δ⟨x∈Δ⟩≡Ε⟨x∈Ε⟩ = x∈Ε , trans Γ⟨x∈Γ⟩≡Δ⟨x∈Δ⟩ Δ⟨x∈Δ⟩≡Ε⟨x∈Ε⟩

≈-preorder : Preorder _ _ _
≈-preorder =  
    record { 
      Carrier = Cxt;
      _≈_ = _≡_;
      _∼_ = _⊆_;
      isPreorder =  record {
        isEquivalence = Relation.Binary.Setoid.isEquivalence (setoid Cxt) ;
        reflexive = λ { {Γ} {.Γ} refl → ρ⊆};
        trans = τ⊆ } }

import Relation.Binary.PreorderReasoning as PreR
open PreR ≈-preorder public

_‚_ : Cxt → K × D → Cxt -- \glq
_‚_ = λ x y → y ∷ x

lemma⊆xy : {x y : K}{d e : D}{Γ : Cxt} → x ≢ y → Γ ‚ x , d ‚ y , e ⊆ Γ ‚ y , e ‚ x , d
lemma⊆xy x≢y (here z≡y) 
  = there (⊥-elim ∘ x≢y ∘ sym ∘ trans (sym z≡y)) (here z≡y) , refl
lemma⊆xy x≢y (there z≢y (here z≡x)) 
  = here z≡x , refl
lemma⊆xy x≢y (there z≢y (there z≢x z∈Γ)) 
  = there z≢x (there z≢y z∈Γ) , refl

lemma⊆xx : {x : K}{d e : D}{Γ : Cxt} → Γ ‚ x , d ‚ x , e ⊆ Γ ‚ x , e
lemma⊆xx (here z≡x) 
  = here z≡x , refl
lemma⊆xx (there z≢x (here z≡x)) 
  = ⊥-elim (z≢x z≡x)
lemma⊆xx (there z≢x (there _ z∈Γ)) 
  = there z≢x z∈Γ , refl

lemma⊆x : {x : K}{d e : D}{Γ : Cxt} → Γ ‚ x , e ⊆ Γ ‚ x , d ‚ x , e 
lemma⊆x (here y≡x)       = here y≡x , refl
lemma⊆x (there y≢x y∈Γ)  = there y≢x (there y≢x y∈Γ) , refl

lemma⊆∷ : {x : K}{d : D}{Γ Δ : Cxt} → Γ ⊆ Δ → Γ ‚ x , d ⊆ Δ ‚ x , d
lemma⊆∷ Γ⊆Δ (here z≡x)       = here z≡x , refl
lemma⊆∷ Γ⊆Δ (there z≢x z∈Γ)  = there z≢x (proj₁ (Γ⊆Δ z∈Γ)) , proj₂ (Γ⊆Δ z∈Γ)

-- _\\_ : Cxt → K → Cxt
-- cxt \\ k = filter (λ y → not (⌊ k ≟ proj₁ y ⌋)) cxt

-- postulate
--   lemma\\→  : (x y : K)(xs : Cxt) → (p : x ∈ xs \\ y) 
--             → x ≢ y × Σ (x ∈ xs) (λ p' → (xs \\ y) ⟨ p ⟩ ≡ xs ⟨ p' ⟩)
--   lemmm\\→dom : (x : K)(xs : Cxt) 
--             → x ∉l dom (xs \\ x)
--   -- lemma\\←  : {x y : K}{xs : Cxt} → x ≢ y → (p : x ∈ xs)
--   --           → Σ (x ∈ xs \\ y) (λ p' → xs ⟨ p ⟩ ≡ (xs \\ y) ⟨ p' ⟩)
--   lemma\\⊆  : (xs : Cxt)(x : K) → xs \\ x ⊆ xs
--   lemma\\⊆, : (xs : Cxt)(x : K)(d : D) → xs ‚ x , d  ⊆ xs \\ x ‚ x , d  
\end{code}


