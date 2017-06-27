module IterationPrincipleTests where

open import Atom
open import Term hiding (fv)
open import Alpha
open import FreeVariables
open import Substitution
open import TermRecursion

open import Function
open import Data.Nat
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

--
-- Test free variables function
--
fv_t1 : fv (v 1) ≡ [ 1 ]
fv_t1 = refl
--
fv_t2 : fv (v 1 · v 2) ≡ 1 ∷ 2 ∷ []
fv_t2 = refl
--
fv_t3 : fv (ƛ 1 (v 1)) ≡ []
fv_t3 = refl
--
fv_t4 : fv (ƛ 1 (v 1 · v 2)) ≡ [ 2 ]
fv_t4 = refl
--
fv_t5 : fv ((ƛ 1 (v 1 · v 2)) · (ƛ 3 (v 4))) ≡ 2 ∷ 4 ∷ []
fv_t5 = refl
--
-- Test substitution operation
-- 
subst_t1 : (v 1) [ 1 ≔ v 2 ] ≡ v 2
subst_t1 = refl
--
subst_t2 : (ƛ 1 (v 1)) [ 1 ≔ v 2 ] ≡ (ƛ 0 (v 0))
subst_t2 = refl
--
subst_t3 : ((ƛ 1 (v 1)) · (v 1)) [ 1 ≔ v 2 ] ≡ ((ƛ 0 (v 0)) · (v 2))
subst_t3 = refl
--
subst_t4 : ((ƛ 0 (v 0)) · (v 1)) [ 1 ≔ v 2 ] ≡ ((ƛ 0 (v 0)) · (v 2))
subst_t4 = refl
--
idTerm : Λ → Λ
idTerm = ΛIt Λ v _·_ ([] , ƛ) 



