module Ahora where

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
open import FreeVariables
open import Chi
open import Relation Λ hiding (_++_)
open import Beta
open import Parallel

open import Data.Bool hiding (_∨_)
open import Data.Nat hiding (_*_)
open import Data.Nat.Properties
open import Data.Empty
open import Data.Sum -- renaming (_⊎_ to _∨_)
open import Data.List
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡ hiding (_⊆_)
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq hiding (trans) renaming ([_] to [_]ᵢ)
open import Relation.Nullary
open import Relation.Nullary.Decidable

⇉ρ : Reflexive _⇉_
⇉ρ {M} = TermIndPerm  (λ M → M ⇉ M) 
                      ⇉v 
                      (λ _ _ → ⇉·) 
                      (λ M y hi → ⇉ƛ [] (λ z _ → hi [ (y , z) ])) 
                      M 
--
lemma-~α⊆⇉ : _∼α_ ⊆ _⇉_
lemma-~α⊆⇉ {M} {N} M~N = lemma⇉αright ⇉ρ M~N 
--
-- ⇉ρ : Reflexive _⇉_
-- ⇉ρ {M} = lemma-~α⊆⇉ ρ
--
lemma→α⊆⇉ : _→α_ ⊆ _⇉_
lemma→α⊆⇉ (inj₁ (ctxinj (▹β {M} {N} {x}))) = ⇉β {M} {M} {N} {N} x x ⇉ρ ⇉ρ ρ
lemma→α⊆⇉ (inj₁ (ctx·l M→αN))              = ⇉· (lemma→α⊆⇉ (inj₁ M→αN)) ⇉ρ
lemma→α⊆⇉ (inj₁ (ctx·r M→αN))              = ⇉· ⇉ρ (lemma→α⊆⇉ (inj₁ M→αN))
lemma→α⊆⇉ (inj₁ (ctxƛ M→αN))               = lemma⇉ƛpres (lemma→α⊆⇉ (inj₁ M→αN))
lemma→α⊆⇉ (inj₂ M~N)                       = lemma-~α⊆⇉ M~N
--
lemma⇉⊆→α* :  _⇉_ ⊆ _→α*_
lemma⇉⊆→α* (⇉v x)           = refl
lemma⇉⊆→α* (⇉ƛ {M} {M'} {x} {y} xs f)        
  with lemma⇉ƛrule (⇉ƛ {M} {M'} {x} {y} xs f)
... | M'' , M⇉M'' , λxM⇉λxM'' , λyM'~λxM'' 
  = begin→
      ƛ x M
    →⟨ abs-star {x} (lemma⇉⊆→α* M⇉M'') ⟩
      ƛ x M''
    →⟨ just (inj₂ (σ λyM'~λxM'')) ⟩
      ƛ y M'
    ▣
lemma⇉⊆→α* (⇉· M⇉M' N⇉N')   = app-star (lemma⇉⊆→α* M⇉M') (lemma⇉⊆→α* N⇉N')
lemma⇉⊆→α* (⇉β {M} {M'} {N} {N'} {P} x y λxM⇉λyM' N⇉N' M'[y:=N']~P) 
  = begin→
      ƛ x M · N
    →⟨ app-star (lemma⇉⊆→α* λxM⇉λyM') (lemma⇉⊆→α* N⇉N') ⟩
      ƛ y M' · N'
    →⟨ just (inj₁ (ctxinj ▹β)) ⟩
      M' [ y ≔ N' ]
    →⟨ just (inj₂ M'[y:=N']~P) ⟩
      P
    ▣
--
lemma-CR⇉ : cr _⇉_
lemma-CR⇉ = diamond-cr diam⇉
--
lemma-CR→α : cr _→α_
lemma-CR→α = cr-⊆ lemma→α⊆⇉ lemma⇉⊆→α* lemma-CR⇉
