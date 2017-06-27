\begin{code}
module Parallel where

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
open import Relation Λ hiding (_++_;trans)
open import Beta

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
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ)
open import Relation.Nullary
open import Relation.Nullary.Decidable
\end{code}

\begin{code}
infixl 3 _⇉_
\end{code}

Parallel reduction.

%<*parallel>
\begin{code}
data _⇉_ : Rel where
  ⇉v :  (x : Atom)
        → v x ⇉ v x
  ⇉ƛ :  {M M' : Λ}{x y : Atom}(xs : List Atom)
        → ((z : Atom) → z ∉ xs → （ x ∙ z ） M ⇉ （ y ∙ z ） M')
        → ƛ x M ⇉ ƛ y M'
  ⇉· :  {M M' N N' : Λ}
        → M ⇉ M' → N ⇉ N'
        → M · N ⇉ M' · N'
  ⇉β :  {M M' N N' P : Λ}(x y : Atom)
        → ƛ x M ⇉ ƛ y M' 
        → N ⇉ N'
        → M' [ y ≔ N' ] ∼α P
        → ƛ x M · N ⇉ P
\end{code}
%</parallel>

\begin{code}
lemma⇉ƛ : {x : Atom}{M N : Λ} → ƛ x M ⇉ N
           → ∃ (λ y → ∃ (λ P → ∃ (λ ys → N ≡ ƛ y P × ((z : Atom) → z ∉ ys → （ x ∙ z ） M ⇉ （ y ∙ z ） P))))
lemma⇉ƛ {x} {M} {ƛ y P} (⇉ƛ ys fys) = y , P , ys , refl , fys 
\end{code}


Parallel diamond property.

\begin{code}
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)

lemma⇉Equiv : EquivariantRel (_⇉_)
lemma⇉Equiv π (⇉v x) 
  = subst (λ H → H ⇉ H) (sym (lemmaπv {x} {π})) (⇉v (π ∙ₐ x))
lemma⇉Equiv π (⇉ƛ {M} {M'} {x} {y} xs fxs) 
  = subst₂  (λ H I → H ⇉ I) (sym (lemmaπƛ {x} {M} {π})) (sym (lemmaπƛ {y} {M'} {π})) 
            (⇉ƛ (xs ++ atoms π) 
                (λ z z∉xs++π →  subst₂  (λ H I → H ⇉ I) 
                                        (  begin≡
                                             π ∙ （ x ∙ z ） M
                                           ≡⟨ lemmaπ∙distributive {x} {z} {M} {π} ⟩
                                             （ π ∙ₐ x ∙ π ∙ₐ z ） (π ∙ M)
                                           ≡⟨ cong (λ H → （ π ∙ₐ x ∙ H ） (π ∙ M)) (lemmaπ∙ₐ≡ {z} {π} (c∉xs++ys→c∉ys {xs = xs} z∉xs++π)) ⟩
                                             （ π ∙ₐ x ∙ z ） (π ∙ M)
                                           □ ) 
                                        (  begin≡
                                             π ∙ （ y ∙ z ） M'
                                           ≡⟨ lemmaπ∙distributive {y} {z} {M'} {π} ⟩
                                             （ π ∙ₐ y ∙ π ∙ₐ z ） (π ∙ M')
                                           ≡⟨ cong (λ H → （ π ∙ₐ y ∙ H ） (π ∙ M')) (lemmaπ∙ₐ≡ {z} {π} (c∉xs++ys→c∉ys {xs = xs} z∉xs++π)) ⟩
                                             （ π ∙ₐ y ∙ z ） (π ∙ M')
                                           □ ) 
                                        (lemma⇉Equiv π (fxs z (c∉xs++ys→c∉xs z∉xs++π)))))
lemma⇉Equiv π (⇉· {M} {M'} {N} {N'} M⇉M' N⇉N') 
  = subst₂  (λ H I → H ⇉ I) (sym (lemmaπ· {M} {N} {π})) (sym (lemmaπ· {M'} {N'} {π})) 
            (⇉· (lemma⇉Equiv π M⇉M') (lemma⇉Equiv π N⇉N'))
lemma⇉Equiv π (⇉β {M} {M'} {N} {N'} {P} x y ƛxM⇉ƛyM' N⇉N' M'[y≔N']∼P) 
  = subst  (λ H → H ⇉ π ∙ P) 
           (sym (trans (lemmaπ· {ƛ x M} {N} {π}) (cong (λ H → H · (π ∙ N)) (lemmaπƛ {x} {M} {π})))) 
           (⇉β  {π ∙ M} {π ∙ M'} {π ∙ N} {π ∙ N'} {π ∙ P} (π ∙ₐ x) (π ∙ₐ y) 
                (subst₂ (λ H I → H ⇉ I) (lemmaπƛ {x} {M} {π}) (lemmaπƛ {y} {M'} {π}) (lemma⇉Equiv π ƛxM⇉ƛyM')) 
                (lemma⇉Equiv π N⇉N') 
                (begin 
                   (π ∙ M') [ π ∙ₐ y ≔ π ∙ N' ] 
                 ∼⟨  σ (lemmaπ[] {M'} {N'} {y} {π})  ⟩
                   π ∙ (M' [ y ≔ N' ]) 
                 ∼⟨ lemma∼αEquiv π M'[y≔N']∼P ⟩
                   π ∙ P
                 ∎))

lemma⇉ƛpres : {x : Atom}{M N : Λ} → M ⇉ N → ƛ x M ⇉ ƛ x N
lemma⇉ƛpres {x} M⇉N =  ⇉ƛ [] ( λ y _ → lemma⇉Equiv [ (x , y) ] M⇉N)

lemma⇉αright : {M N P : Λ} → M ⇉ N → N ∼α P → M ⇉ P
lemma⇉αright (⇉v a)          ∼αv
  = ⇉v a
lemma⇉αright (⇉· M⇉M' N⇉N')  (∼α· M'∼P N'∼P') 
  = ⇉· (lemma⇉αright M⇉M' M'∼P) (lemma⇉αright N⇉N' N'∼P')
lemma⇉αright (⇉ƛ xs fxs)     (∼αƛ ys fys) 
  = ⇉ƛ  (xs ++ ys) 
        (λ z z∉xs++ys → lemma⇉αright (fxs z (c∉xs++ys→c∉xs z∉xs++ys)) (fys z (c∉xs++ys→c∉ys {xs = xs} z∉xs++ys)))
lemma⇉αright (⇉β x y ƛxM⇉ƛyM' N⇉N' M'[y≔N']∼N) N∼P 
  = ⇉β x y ƛxM⇉ƛyM' N⇉N' (τ M'[y≔N']∼N N∼P)

lemma⇉αleft : {M N P : Λ} → M ∼α N → N ⇉ P → M ⇉ P
lemma⇉αleft ∼αv          (⇉v a)
  = ⇉v a
lemma⇉αleft (∼αƛ xs fxs) (⇉ƛ ys fys) 
  = ⇉ƛ (xs ++ ys) (λ z z∉xs++ys → lemma⇉αleft (fxs z (c∉xs++ys→c∉xs z∉xs++ys)) (fys z (c∉xs++ys→c∉ys {xs = xs} z∉xs++ys)))
lemma⇉αleft (∼α· M∼M' N∼N') (⇉· M'⇉P N'⇉P') 
  = ⇉· (lemma⇉αleft M∼M' M'⇉P) (lemma⇉αleft N∼N' N'⇉P')
lemma⇉αleft (∼α· {ƛ z M} {ƛ .x N} {M'} {N'} ƛzM∼ƛxN M'∼N') (⇉β x y ƛxN⇉ƛyP' N'⇉P'' P'[x≔P'']∼P) 
  = ⇉β z y (lemma⇉αleft ƛzM∼ƛxN ƛxN⇉ƛyP') (lemma⇉αleft M'∼N' N'⇉P'') P'[x≔P'']∼P
lemma⇉αleft (∼α· {v _}   {ƛ .x N} {M'} {N'} () M'∼N') (⇉β x y ƛxN⇉ƛyP' N'⇉P'' P'[x≔P'']∼P) 
lemma⇉αleft (∼α· {_ · _} {ƛ .x N} {M'} {N'} () M'∼N') (⇉β x y ƛxN⇉ƛyP' N'⇉P'' P'[x≔P'']∼P) 

P⇉# : Atom → Λ → Set
P⇉# x M = {N : Λ} → x # M → M ⇉ N → x # N

αCompP⇉# : (x : Atom) → αCompatiblePred (P⇉# x)
αCompP⇉# x {M} {P} M~P PM x#P P⇉N = PM (lemma∼α# (σ M~P) x#P) (lemma⇉αleft M~P P⇉N)

lemma⇉# : {M : Λ}{x : Atom} → P⇉# x M
lemma⇉# {M} {x} = TermαIndPerm
                      (P⇉# x)
                      (αCompP⇉# x)
                      lemmav
                      lemma·
                      ([ x ] , lemmaƛ)
                      M
   where
   lemmav : (a : ℕ) → P⇉# x (v a)
   lemmav a x#a (⇉v .a) 
     = x#a
   lemma· : (M P : Λ) → P⇉# x M → P⇉# x P → P⇉# x (M · P)
   lemma· M P PM PP (#· x#M x#P) (⇉· M⇉N' P⇉N'') 
     = #· (PM x#M M⇉N') (PP x#P P⇉N'')
   lemma· (ƛ .y M) P PƛyM PP (#· x#ƛyM x#P) (⇉β y z ƛyM⇉ƛzN' P⇉N'' N'[z:=N'']∼N)
     = lemma∼α# N'[z:=N'']∼N (lemma#Subst (PƛyM x#ƛyM ƛyM⇉ƛzN') (PP x#P P⇉N''))
   lemmaƛ : (M : Λ) (b : ℕ) → b ∉ [ x ] → (∀ π → P⇉# x (π ∙ M)) → P⇉# x (ƛ b M)
   lemmaƛ M .x  x∉[x] PπM {ƛ y N} #ƛ≡       (⇉ƛ xs fxs) 
     = ⊥-elim (x∉[x] (here refl))
   lemmaƛ M b   b∉[x] PπM {ƛ y N} (#ƛ x#M)  (⇉ƛ xs fxs) 
     = corollarylemma*swap→ x≢z (PπM [ ( b , z ) ] x#（bz）M (fxs z z∉xs))
     where 
     z = χ' (x ∷ fv N ++ xs)
     z∉x∷fvM++xs = lemmaχ∉ (x ∷ fv N ++ xs)
     z∉xs : z ∉ xs
     z∉xs = c∉xs++ys→c∉ys  {xs = fv N} (b∉a∷xs→b∉xs z∉x∷fvM++xs)
     x≢z : x ≢ z
     x≢z = sym≢ (b∉a∷xs→b≢a z∉x∷fvM++xs)
     x≢b : x ≢ b
     x≢b x≡b = ⊥-elim (b∉[x] (here (sym x≡b)))
     x#（bz）M : x # （ b ∙ z ） M
     x#（bz）M = lemma#swap≢ x≢b x≢z x#M

-- lemma⇉#         u#x   (⇉v x)  
--   = u#x
-- lemma⇉# {x = u} u#ƛyM (⇉ƛ {M} {N} {x} {y} xs fxs) 
--   = corollarylemma*swap→ u≢z u#（yz）M
--   where
--   z = χ' (u ∷ (fv M ++ xs))
--   z∉u∷fvM++xs = χ'∉ (u ∷ (fv M ++ xs))
--   z∉xs : z ∉ xs
--   z∉xs = c∉xs++ys→c∉ys  {xs = fv M} (b∉a∷xs→b∉xs z∉u∷fvM++xs)
--   u≢z : u ≢ z
--   u≢z = sym≢ (b∉a∷xs→b≢a z∉u∷fvM++xs)
--   z#M : z # M
--   z#M =  lemma∉fv→# (c∉xs++ys→c∉xs (b∉a∷xs→b∉xs z∉u∷fvM++xs)) 
--   u#（xz）M : u # （ x ∙ z ） M
--   u#（xz）M = lemma#swapƛ z#M u≢z u#ƛyM
--   u#（yz）M : u # （ y ∙ z ） N
--   u#（yz）M = lemma⇉# u#（xz）M (fxs z z∉xs)
-- lemma⇉# (#· x#M x#M') (⇉· M⇉N M'⇉N') 
--   = #· (lemma⇉# x#M M⇉N) (lemma⇉# x#M' M'⇉N')
-- lemma⇉# (#· x#ƛyM x#M') (⇉β y z ƛyM⇉ƛzN M'⇉N' N[z≔N']∼P) 
--   = lemma∼α# N[z≔N']∼P (lemma#Subst (lemma⇉# x#ƛyM ƛyM⇉ƛzN) (lemma⇉# x#M' M'⇉N'))

lemma⇉ƛrule : {M M' : Λ}{x : Atom}
        → ƛ x M ⇉ M'
        → Σ Λ (λ M″ → M ⇉ M″ × ƛ x M ⇉ ƛ x M″ × M' ∼α ƛ x M″) 
lemma⇉ƛrule {M} {ƛ y M'} {x} (⇉ƛ xs fxs) 
  =  （ y ∙ x ） M'                            , 
     M⇉（yx）M'                                , 
     lemma⇉αright (⇉ƛ xs fxs) ƛyM'∼ƛx（yx）M'  , 
     ƛyM'∼ƛx（yx）M'
  where
  x#ƛyM' : x # ƛ y M'
  x#ƛyM' = lemma⇉# #ƛ≡ (⇉ƛ xs fxs)
  ƛyM'∼ƛx（yx）M' : ƛ y M' ∼α ƛ x (（ y ∙ x ） M')
  ƛyM'∼ƛx（yx）M' = lemma∼αλ' x#ƛyM'
  z : Atom
  z = χ' (xs ++ fv (ƛ y M'))
  z∉xs : z ∉ xs
  z∉xs = c∉xs++ys→c∉xs (lemmaχ∉ (xs ++ fv (ƛ y M')))
  z#ƛyM' : z # ƛ y M'
  z#ƛyM' = lemma∉fv→# (c∉xs++ys→c∉ys {xs = xs} (lemmaχ∉ (xs ++ fv (ƛ y M')))) 
  M⇉（yx）M' : M ⇉ （ y ∙ x ） M'
  M⇉（yx）M' = lemma⇉αright 
                 (subst (λ H → H ⇉ （ x ∙ z ） （ y ∙ z ） M') lemma（ab）（ab）M≡M (lemma⇉Equiv [ (x , z) ] (fxs z z∉xs))) 
                 (  begin
                      （ x ∙ z ） （ y ∙ z ） M'
                    ≈⟨ lemma∙comm ⟩
                      （ z ∙ x ） （ y ∙ z ） M'
                    ∼⟨ lemma∙cancel∼α'' x#ƛyM' z#ƛyM' ⟩
                      （ y ∙ x ） M'
                    ∎    )

lemma⇉βrule : {M M' N N' P : Λ}(x y : Atom)
        → ƛ x M ⇉ ƛ y M' 
        → N ⇉ N'
        → M' [ y ≔ N' ] ∼α P
        → Σ Λ (λ M″ → ƛ x M ⇉ ƛ x M″ × M″ [ x ≔ N' ] ∼α P) 
lemma⇉βrule {M} {M'} {N} {N'} {P} x y ƛxM⇉ƛyM' N⇉N' M'[y≔N']∼P 
  =  （ y ∙ x ） M'                              ,
     lemma⇉αright  ƛxM⇉ƛyM' (lemma∼αλ' x#ƛyM')  , 
     (  begin
          (（ y ∙ x ） M') [ x ≔ N' ]
        ≈⟨  cong (λ H → H [ x ≔ N' ]) (lemma∙comm {y} {x} {M'}) ⟩ 
          (（ x ∙ y ） M') [ x ≔ N' ]
        ∼⟨ lemmaSwapSubstVar' x y N' M' x#ƛyM' ⟩ 
          M' [ y ≔ N' ]
        ∼⟨ M'[y≔N']∼P  ⟩ 
          P
        ∎    ) 
  where
  x#ƛyM' : x # ƛ y M'
  x#ƛyM' = lemma⇉# #ƛ≡ ƛxM⇉ƛyM'
\end{code}

-- %<*parallel2>
-- \begin{code}
-- data _⇉2_ : Λ → Λ → Set where
--   ⇉v :  (x : Atom)
--         → v x ⇉2 v x
--   ⇉ƛ :  {M M' : Λ}{x : Atom}
--         → M ⇉2 M'
--         → ƛ x M ⇉2 ƛ x M'
--   ⇉· :  {M M' N N' : Λ}
--         → M ⇉2 M' → N ⇉2 N'
--         → M · N ⇉2 M' · N'
--   ⇉β :  {M M' N N' P : Λ}(x : Atom)
--         → ƛ x M ⇉2 ƛ x M' 
--         → N ⇉2 N'
--         → M' [ x ≔ N' ] ∼α P
--         → ƛ x M · N ⇉2 P
-- \end{code}
-- %</parallel2>


-- \begin{code}
-- lemma⇉to⇉2 : {M N : Λ} → M ⇉ N → M ⇉2 N
-- lemma⇉to⇉2 (⇉v x)                = ⇉v x
-- lemma⇉to⇉2 (⇉ƛ xs f)
--   with lemma⇉ƛrule (⇉ƛ xs f)
-- ... | M″ , M⇉M″ , _ , ƛyN~ƛxM″
--   = {! ⇉ƛ !}
-- lemma⇉to⇉2 (⇉· M⇉M' N⇉N')        = {!!}
-- lemma⇉to⇉2 (⇉β x y M⇉M' N⇉N' f)  = {!!}
-- \end{code}

\begin{code}
P⇉[] : {N N' : Λ}(x : Atom) → Λ → Set
P⇉[] {N} {N'} x M = {M' : Λ} → M ⇉ M' → N ⇉ N' → M [ x ≔ N ] ⇉ M' [ x ≔ N' ]

αCompP⇉[] : {N N' : Λ}(x : Atom) → αCompatiblePred (P⇉[] {N} {N'} x)
αCompP⇉[] {N} {N'} x {M} {P} M∼P P⇉[]M {M'} P⇉M' N⇉N' 
  = subst (λ H → H ⇉ (M' [ x ≔ N' ])) (lemmaSubst1 N x M∼P) (P⇉[]M (lemma⇉αleft M∼P P⇉M') N⇉N')

lemma⇉Subst : {N N' : Λ}(x : Atom)(M : Λ) → P⇉[] {N} {N'} x M
lemma⇉Subst {N} {N'} x M 
  = TermαPrimInd2  (P⇉[] {N} {N'} x) 
                   (x ∷ fv N ++ fv N')
                   (αCompP⇉[] {N} {N'} x) 
                   lemmav 
                   lemma· 
                   lemmaƛ 
                   M
  where
  lemmav : (a : ℕ) → P⇉[] {N} {N'} x (v a)
  lemmav a (⇉v .a) N⇉N' with x ≟ₐ a
  ... | yes  _ = N⇉N'
  ... | no   _ = ⇉v a
  lemma· : (P Q : Λ) 
    → P⇉[] {N} {N'} x P 
    → P⇉[] {N} {N'} x Q 
    → ((c : ℕ) → c ∈ x ∷ fv N ++ fv N' → c ∉b P · Q) 
    → P⇉[] {N} {N'} x (P · Q)
  lemma· P Q hiP hiQ f∉ .{P' · Q'} 
         (⇉· .{P} {P'} .{Q} {Q'} P⇉P' Q⇉Q') 
         N⇉N' 
    = ⇉· (hiP P⇉P' N⇉N') (hiQ Q⇉Q' N⇉N')
  lemma· (ƛ .y P) Q hiƛyP hiQ f∉ {M'} 
         (⇉β .{P} {P'} .{Q} {Q'} .{M'} y z (⇉ƛ xs ∀w∉xs（yw）P⇉（zw）P') Q⇉Q' P'[z≔Q']∼M') 
         N⇉N' 
    with lemma⇉βrule y z (⇉ƛ xs ∀w∉xs（yw）P⇉（zw）P') Q⇉Q' P'[z≔Q']∼M'
  ... | P″ , ƛyP⇉ƛyP″ , P″[y≔N']∼M'
    = lemma⇉αleft
            (  begin
                 ((ƛ y P) · Q) [ x ≔ N ]
               ≈⟨ refl ⟩
                 (ƛ y P) [ x ≔ N ] · Q [ x ≔ N ] 
               ∼⟨ ∼α· (lemmaƛ∼[] P y∉x∷fvN) ρ ⟩
                 (ƛ y (P [ x ≔ N ])) · Q [ x ≔ N ]
               ∎   )        
            (⇉β  {P [ x ≔ N ]} {P″ [ x ≔ N' ]} 
                 {Q [ x ≔ N ]} {Q' [ x ≔ N' ]} 
                 {M' [ x ≔ N' ]} y y 
                 (lemma⇉αleft  (  begin
                                    ƛ y (P [ x ≔ N ])
                                  ∼⟨ σ (lemmaƛ∼[] P y∉x∷fvN) ⟩
                                    (ƛ y P) [ x ≔ N ]
                                  ∎                    ) 
                               (lemma⇉αright  (hiƛyP ƛyP⇉ƛyP″ N⇉N') 
                                              (  begin
                                                   (ƛ y P″) [ x ≔ N' ]
                                                 ∼⟨ lemmaƛ∼[] P″ y∉x∷fvN' ⟩
                                                   ƛ y (P″ [ x ≔ N' ])
                                                 ∎                      ))) 
                 (hiQ Q⇉Q' N⇉N') 
                 (  begin
                      (P″ [ x ≔ N' ]) [ y ≔ Q' [ x ≔ N' ] ]
                    ∼⟨ σ (lemmaSubstComposition Q' P″ y∉x∷fvN') ⟩
                      (P″ [ y ≔ Q' ]) [ x ≔ N' ] 
                    ≈⟨ lemmaSubst1 N' x P″[y≔N']∼M' ⟩
                      M' [ x ≔ N' ]
                    ∎                                         )            ) 
    where
    y∉x∷fvN++fvN' : y ∉ x ∷ (fv N ++ fv N')
    y∉x∷fvN++fvN' y∈x∷fvN++fvN' with f∉ y y∈x∷fvN++fvN'
    ... | ∉b· (∉bƛ y≢y _) _ = ⊥-elim (y≢y refl)
    y∉x∷fvN : y ∉ x ∷ fv N 
    y∉x∷fvN = c∉x∷xs++ys→c∉x∷xs y∉x∷fvN++fvN'
    y∉x∷fvN' : y ∉ x ∷ fv N'
    y∉x∷fvN' = c∉x∷xs++ys→c∉x∷ys {xs = fv N} y∉x∷fvN++fvN'
  lemmaƛ : (P : Λ) (b : ℕ) 
    → P⇉[] {N} {N'} x P 
    → ((c : ℕ) → c ∈ x ∷ fv N ++ fv N' → c ∉b ƛ b P) 
    → P⇉[] {N} {N'} x (ƛ b P)
  lemmaƛ P b hiP f∉ {Q} ⇉ƛbP⇉Q N⇉N'
    with lemma⇉ƛrule ⇉ƛbP⇉Q
  ... | P″ , P⇉P″ ,  ƛbP⇉ƛbP″ , Q∼ƛbP″
    = lemma⇉αright  (lemma⇉αleft (lemmaƛ∼[] P b∉x∷fvN) (lemma⇉ƛpres {b} (hiP P⇉P″ N⇉N'))) 
                    (  begin
                         ƛ b (P″ [ x ≔ N' ]) 
                       ∼⟨ σ (lemmaƛ∼[] P″ b∉x∷fvN')    ⟩
                         (ƛ b P″)  [ x ≔ N' ]
                       ≈⟨ lemmaSubst1 N' x (σ Q∼ƛbP″)  ⟩
                         Q         [ x ≔ N' ]
                       ∎  )
    where
    b∉x∷fvN++fvN' : b ∉ x ∷ (fv N ++ fv N')
    b∉x∷fvN++fvN' b∈x∷fvN++fvN' with f∉ b b∈x∷fvN++fvN'
    ... | ∉bƛ b≢b _ = ⊥-elim (b≢b refl)
    b∉x∷fvN : b ∉ x ∷ fv N 
    b∉x∷fvN = c∉x∷xs++ys→c∉x∷xs b∉x∷fvN++fvN'
    b∉x∷fvN' : b ∉ x ∷ fv N'
    b∉x∷fvN' = c∉x∷xs++ys→c∉x∷ys {xs = fv N} b∉x∷fvN++fvN'
\end{code}
    
-- lemma⇉Subst : {N N' : Λ}(x : Atom)(M : Λ){M' : Λ} → M ⇉ M' → N ⇉ N' → M [ x ≔ N ] ⇉ M' [ x ≔ N' ]
-- lemma⇉Subst {N} {N'} x (v y)         (⇉v .y)                         N⇉N'      
--   with x ≟ₐ y
-- ... | yes  _ = N⇉N'
-- ... | no   _ = ⇉v y
-- lemma⇉Subst x (M · P)       (⇉· M⇉M' P⇉P') N⇉N'
--   = ⇉· (lemma⇉Subst x M M⇉M' N⇉N') (lemma⇉Subst x P P⇉P' N⇉N')
-- lemma⇉Subst {N} {N'} x (ƛ y M)       (⇉ƛ .{M} {M'} .{y} {z} xs fxs)  N⇉N'      
--   = proof
--   where 
--   ws = ((x ∷ fv N) ++ (x ∷ fv N') ++ xs ++ ocurr M ++ ocurr M')
--   w = χ' ws
--   w∉ws : w ∉ ws
--   w∉ws = χ'∉ ws
--   w#M : w # M
--   w#M = lemma∉→# (lemmaocurr (c∉xs++ys→c∉xs (c∉xs++ys→c∉ys {xs = xs} (c∉xs++ys→c∉ys {xs = x ∷ fv N'} (c∉xs++ys→c∉ys {xs = x ∷ fv N} w∉ws)))))
--   w#M' : w # M'
--   w#M' = lemma∉→# (lemmaocurr (c∉xs++ys→c∉ys {xs = ocurr M} (c∉xs++ys→c∉ys {xs = xs} (c∉xs++ys→c∉ys {xs = x ∷ fv N'} (c∉xs++ys→c∉ys {xs = x ∷ fv N} w∉ws)))))
--   w∉xs : w ∉ xs
--   w∉xs = c∉xs++ys→c∉xs (c∉xs++ys→c∉ys {xs = x ∷ fv N'} (c∉xs++ys→c∉ys {xs = x ∷ fv N} w∉ws))
--   w∉x∷fvN : w ∉ x ∷ fv N
--   w∉x∷fvN = c∉xs++ys→c∉xs w∉ws
--   w∉x∷fvN' : w ∉ x ∷ fv N'
--   w∉x∷fvN' = c∉xs++ys→c∉xs (c∉xs++ys→c∉ys {xs = x ∷ fv N} w∉ws)
--   ƛyM∼ƛw（yw）M : ƛ y M ∼α ƛ w (（ y ∙ w ） M)
--   ƛyM∼ƛw（yw）M = lemma∼αλ w#M
--   ƛzM'∼ƛw（zw）M' : ƛ z M' ∼α ƛ w (（ z ∙ w ） M')
--   ƛzM'∼ƛw（zw）M' = lemma∼αλ w#M'
--   ƛyM[x≔N]≡ƛw（yw）M[x≔N] :  (ƛ y M) [ x ≔ N ] ≡ (ƛ w (（ y ∙ w ） M)) [ x ≔ N ]
--   ƛyM[x≔N]≡ƛw（yw）M[x≔N] = lemmaSubst1 N x ƛyM∼ƛw（yw）M
--   ƛzM'[x≔N]≡ƛw（zw）M'[x≔N] :  (ƛ z M') [ x ≔ N' ] ≡ (ƛ w (（ z ∙ w ） M')) [ x ≔ N' ]
--   ƛzM'[x≔N]≡ƛw（zw）M'[x≔N] = lemmaSubst1 N' x ƛzM'∼ƛw（zw）M'
--   ƛw（yw）M[x≔N]∼ƛw（（yw）M[x≔N]） : (ƛ w (（ y ∙ w ） M)) [ x ≔ N ] ∼α ƛ w (((（ y ∙ w ） M)) [ x ≔ N ])
--   ƛw（yw）M[x≔N]∼ƛw（（yw）M[x≔N]） = lemmaƛ∼[] (（ y ∙ w ） M) w∉x∷fvN
--   ƛw（zw）M'[x≔N]∼ƛw（（zw）M'[x≔N]） : (ƛ w (（ z ∙ w ） M')) [ x ≔ N' ] ∼α ƛ w (((（ z ∙ w ） M')) [ x ≔ N' ])
--   ƛw（zw）M'[x≔N]∼ƛw（（zw）M'[x≔N]） = lemmaƛ∼[] (（ z ∙ w ） M') w∉x∷fvN'
--   proof' : (ƛ w (（ y ∙ w ） M)) [ x ≔ N ] ⇉ (ƛ w (（ z ∙ w ） M')) [ x ≔ N' ]
--   proof' = lemma⇉αleft ƛw（yw）M[x≔N]∼ƛw（（yw）M[x≔N]） (lemma⇉αright (⇉ƛ ws (λ u u∉ws →  lemma⇉Equiv [ ( w , u ) ] (lemma⇉Subst x (（ y ∙ w ） M) (fxs w w∉xs) N⇉N'))) (σ ƛw（zw）M'[x≔N]∼ƛw（（zw）M'[x≔N]）))
--   proof : ƛ y M [ x ≔ N ] ⇉ ƛ z M' [ x ≔ N' ]
--   proof = subst₂ (λ T U → T ⇉ U) (sym ƛyM[x≔N]≡ƛw（yw）M[x≔N]) (sym ƛzM'[x≔N]≡ƛw（zw）M'[x≔N]) proof'
-- lemma⇉Subst {N} {N'} x (ƛ .y P · Q)  (⇉β .{P} {P'} .{Q} {Q'} {M} y z ƛyP⇉ƛzP' Q⇉Q' P'[z≔Q']∼M) N⇉N' 
--   = proof
--   where
--   us = (x ∷ fv N) ++ ocurr P
--   u = χ' us
--   u∉us = χ'∉ us
--   u∉x∷fvN : u ∉ x ∷ fv N
--   u∉x∷fvN = c∉xs++ys→c∉xs u∉us
--   ws = (x ∷ fv N') ++ ocurr P'
--   w = χ' ws
--   w∉ws = χ'∉ ws
--   u#P : u # P
--   u#P = lemma∉→# (lemmaocurr  (c∉xs++ys→c∉ys {xs = x ∷ fv N} u∉us))
--   w#P' : w # P'
--   w#P' = lemma∉→# (lemmaocurr  (c∉xs++ys→c∉ys {xs = x ∷ fv N'} w∉ws))
--   w∉x∷fvN' : w ∉ x ∷ fv N'
--   w∉x∷fvN' = c∉xs++ys→c∉xs w∉ws
--   ƛyP∼ƛu（yu）P' : ƛ y P ∼α ƛ u (（ y ∙ u ） P)
--   ƛyP∼ƛu（yu）P' = lemma∼αλ u#P
--   ƛyP[x≔N]∼ƛu（（yu）P[x≔N]） : ƛ y P [ x ≔ N ] ∼α ƛ u ((（ y ∙ u ） P) [ x ≔ N ])
--   ƛyP[x≔N]∼ƛu（（yu）P[x≔N]） =  begin
--                                  ƛ y P [ x ≔ N ]
--                                ≈⟨ lemmaSubst1 N x ƛyP∼ƛu（yu）P'  ⟩
--                                  (ƛ u (（ y ∙ u ） P)) [ x ≔ N ]
--                                ∼⟨ lemmaƛ∼[] (（ y ∙ u ） P) u∉x∷fvN ⟩
--                                  ƛ u ((（ y ∙ u ） P) [ x ≔ N ])
--                                ∎
--   ƛzP'∼ƛw（zw）P' : ƛ z P' ∼α ƛ w (（ z ∙ w ） P')
--   ƛzP'∼ƛw（zw）P' = lemma∼αλ w#P'
--   ƛzP'[x≔N']∼ƛw（（zw）P'[x≔N]） : ƛ z P' [ x ≔ N' ] ∼α ƛ w ((（ z ∙ w ） P') [ x ≔ N' ])
--   ƛzP'[x≔N']∼ƛw（（zw）P'[x≔N]） =  begin
--                                     ƛ z P' [ x ≔ N' ]
--                                   ≈⟨ lemmaSubst1 N' x ƛzP'∼ƛw（zw）P'  ⟩
--                                    (ƛ w (（ z ∙ w ） P')) [ x ≔ N' ]
--                                   ∼⟨ lemmaƛ∼[] (（ z ∙ w ） P') w∉x∷fvN' ⟩                                   
--                                     ƛ w ((（ z ∙ w ） P') [ x ≔ N' ])
--                                   ∎
--   hiƛyP : ƛ y P [ x ≔ N ] ⇉ ƛ z P' [ x ≔ N' ]
--   hiƛyP = lemma⇉Subst x (ƛ y P) ƛyP⇉ƛzP' N⇉N'
--   ƛu（（yu）P[x≔N]）⇉ƛw（（zw）P'[x≔N']） : ƛ u ((（ y ∙ u ） P) [ x ≔ N ]) ⇉ ƛ w ((（ z ∙ w ） P') [ x ≔ N' ])
--   ƛu（（yu）P[x≔N]）⇉ƛw（（zw）P'[x≔N']） = lemma⇉αleft (σ ƛyP[x≔N]∼ƛu（（yu）P[x≔N]）) (lemma⇉αright hiƛyP ƛzP'[x≔N']∼ƛw（（zw）P'[x≔N]）)
--   hiQ : Q [ x ≔ N ] ⇉ Q' [ x ≔ N' ]
--   hiQ = lemma⇉Subst x Q Q⇉Q' N⇉N'
--   proof' : ƛ u ((（ y ∙ u ） P) [ x ≔ N ]) · Q [ x ≔ N ] ⇉ (（ z ∙ w ） P') [ x ≔ N' ] [ w ≔ Q' [ x ≔ N' ] ]
--   proof' = ⇉β u w ƛu（（yu）P[x≔N]）⇉ƛw（（zw）P'[x≔N']） hiQ ρ
--   M[x≔N']∼α（（zw）P'）[x≔N'][w≔Q'[x≔N']] : M [ x ≔ N' ] ∼α (（ z ∙ w ） P') [ x ≔ N' ] [ w ≔ Q' [ x ≔ N' ] ]
--   M[x≔N']∼α（（zw）P'）[x≔N'][w≔Q'[x≔N']]
--     = begin
--       M [ x ≔ N' ]
--     ≈⟨ lemmaSubst1 N' x (σ P'[z≔Q']∼M) ⟩
--       P' [ z ≔ Q' ] [ x ≔ N' ]
--     ≈⟨ lemmaSubst1 N' x (σ (lemmaSwapSubstVar w z Q' P' w#P')) ⟩
--       (（ w ∙ z ） P') [ w ≔ Q' ] [ x ≔ N' ]
--     ≈⟨ cong (λ H → H [ w ≔ Q' ] [ x ≔ N' ]) (lemma∙comm {w} {z} {P'}) ⟩
--       (（ z ∙ w ） P') [ w ≔ Q' ] [ x ≔ N' ]
--     ∼⟨ lemmaSubstComposition {w} {x} {N'} Q' (（ z ∙ w ） P') w∉x∷fvN' ⟩
--       (（ z ∙ w ） P') [ x ≔ N' ] [ w ≔ Q' [ x ≔ N' ] ]
--     ∎
--   proof : (ƛ y P · Q) [ x ≔ N ] ⇉ M [ x ≔ N' ]
--   proof = lemma⇉αleft (∼α· ƛyP[x≔N]∼ƛu（（yu）P[x≔N]） ρ) (lemma⇉αright proof' (σ M[x≔N']∼α（（zw）P'）[x≔N'][w≔Q'[x≔N']]))

-- corollary⇉Equiv : (M N : Λ)(x y z : Atom) → y ∉ₜ M → z ∉ₜ M  → （ x ∙ y ） M ⇉ N → （ x ∙ z ） M ⇉ （ y ∙ z ） N
-- corollary⇉Equiv _ N _ y z y∉S z∉S （xy）M⇉N 
--   = subst  (λ T → T ⇉ （ y ∙ z ） N) 
--            (lemma∙cancel z∉S y∉S) 
--            (lemma⇉Equiv [ ( y , z ) ] （xy）M⇉N)

-- diam⇉ :  {M N P : Λ} → M ⇉ N → M ⇉ P
--          → ∃ (λ Q → N ⇉ Q × P ⇉ Q)
-- diam⇉  (⇉v x) (⇉v .x)
--   = v x , ⇉v x , ⇉v x 
-- diam⇉  {ƛ x M} {ƛ y N} {ƛ z P} 
--        (⇉ƛ xs fxs) (⇉ƛ ys fys)
--   =  ƛ u R                                                                                    , 
--      ⇉ƛ zs (λ w w∉zs → corollary⇉Equiv N R y u w (∀w∉zs→w∉N u∉zs) (∀w∉zs→w∉N w∉zs) （yu）N⇉R)  ,
--      ⇉ƛ zs (λ w w∉zs → corollary⇉Equiv P R z u w (∀w∉zs→w∉P u∉zs) (∀w∉zs→w∉P w∉zs) （zu）P⇉R) 
--   where
--   zs = (xs ++ ys) ++ (ocurr N ++ ocurr P)
--   u : Atom
--   u = χ' zs
--   u∉zs : u ∉ zs
--   u∉zs = χ'∉ zs
--   u∉xs++ys : u ∉ xs ++ ys
--   u∉xs++ys = c∉xs++ys→c∉xs {u} {xs ++ ys} u∉zs
--   ∀w∉zs→w∉N : {w : Atom} → w ∉ zs → w ∉ₜ N
--   ∀w∉zs→w∉N {w} w∉zs = lemmaocurr (c∉xs++ys→c∉xs {w} {ocurr N} (c∉xs++ys→c∉ys {w} {xs ++ ys} w∉zs))
--   ∀w∉zs→w∉P : {w : Atom} → w ∉ zs → w ∉ₜ P
--   ∀w∉zs→w∉P {w} w∉zs = lemmaocurr (c∉xs++ys→c∉ys {w} {ocurr N} (c∉xs++ys→c∉ys {w} {xs ++ ys} w∉zs))
--   hi : (w : Atom) → (w ∉ xs ++ ys) → ∃ (λ R → （ y ∙ w ） N ⇉ R × （ z ∙ w ） P ⇉ R)
--   hi w w∉xs++ys = diam⇉ (fxs w (c∉xs++ys→c∉xs w∉xs++ys)) (fys w (c∉xs++ys→c∉ys {w} {xs} w∉xs++ys)) -- induccion en la relación !
--   R : Λ 
--   R = proj₁ (hi u u∉xs++ys)
--   （yu）N⇉R : （ y ∙ u ） N ⇉ R
--   （yu）N⇉R = proj₁ (proj₂ (hi u u∉xs++ys))
--   （zu）P⇉R : （ z ∙ u ） P ⇉ R
--   （zu）P⇉R = proj₂ (proj₂ (hi u u∉xs++ys))
-- diam⇉  {ƛ x M · N} {P} {Q} 
--        (⇉β .{M} {P'} .{N} {P''} .x y (⇉ƛ xs fxs) N⇉P'' P'[y≔P'']∼P) 
--        (⇉β .{M} {Q'} .{N} {Q''} .x z (⇉ƛ ys fys) N⇉Q'' Q'[z≔Q'']∼Q)
--   =  R' [ u ≔ R'' ]                                                                 ,
--      lemma⇉αleft (σ P'[y≔P'']∼P)
--                  (lemma⇉αright  P'[y≔P'']⇉（yu）R'[y≔R''] （yu）R'[y≔R'']∼R'[u≔R''])  ,
--      lemma⇉αleft (σ Q'[z≔Q'']∼Q)
--                  (lemma⇉αright  Q'[z≔Q'']⇉（zu）R'[z≔R''] （zu）R'[z≔R'']∼R'[u≔R''])
--   where
--   zs = (y ∷ z ∷ ocurr P' ++ ocurr Q') ++ (xs ++ ys)
--   u : Atom
--   u = χ' zs
--   u∉zs : u ∉ zs
--   u∉zs = χ'∉ zs
--   u∉xs++ys : u ∉ xs ++ ys
--   u∉xs++ys = c∉xs++ys→c∉ys {xs = y ∷ z ∷ ocurr P' ++ ocurr Q'} u∉zs
--   hiu : ∃ (λ R → （ y ∙ u ） P' ⇉ R × （ z ∙ u ） Q' ⇉ R)
--   hiu = diam⇉ (fxs u (c∉xs++ys→c∉xs u∉xs++ys)) (fys u (c∉xs++ys→c∉ys {u} {xs} u∉xs++ys))
--   R' : Λ
--   R' = proj₁ hiu
--   （yu）P'⇉R' : （ y ∙ u ） P' ⇉  R'
--   （yu）P'⇉R' = (proj₁ (proj₂ hiu))
--   （zu）Q'⇉R' : （ z ∙ u ） Q' ⇉  R'
--   （zu）Q'⇉R' = (proj₂ (proj₂ hiu))
--   u≢y : u ≢ y
--   u≢y u≡y = ⊥-elim (u∉zs (here u≡y))
--   u#P' : u # P'
--   u#P' = lemma∉→# (lemmaocurr (c∉xs++ys→c∉xs (d∉ab∷xs→d∉xs (c∉xs++ys→c∉xs u∉zs)))) 
--   u#Q' : u # Q'
--   u#Q' = lemma∉→# (lemmaocurr (c∉xs++ys→c∉ys {xs = ocurr P'} (d∉ab∷xs→d∉xs (c∉xs++ys→c∉xs u∉zs)))) 
--   y#（yu）P' : y # （ y ∙ u ） P'
--   y#（yu）P' = lemma#swap u#P'
--   z#（zu）Q' : z # （ z ∙ u ） Q'
--   z#（zu）Q' = lemma#swap u#Q'
--   P'⇉（yu）R' : P' ⇉ （ y ∙ u ） R'
--   P'⇉（yu）R' = subst (λ S → S ⇉ （ y ∙ u ） R') lemma（ab）（ab）M≡M (lemma⇉Equiv [ ( y , u ) ] （yu）P'⇉R')
--   Q'⇉（zu）R' : Q' ⇉ （ z ∙ u ） R'
--   Q'⇉（zu）R' = subst (λ S → S ⇉ （ z ∙ u ） R') lemma（ab）（ab）M≡M (lemma⇉Equiv [ ( z , u ) ] （zu）Q'⇉R')
--   hi : ∃ (λ R → P'' ⇉ R × Q'' ⇉ R)
--   hi  = diam⇉ N⇉P'' N⇉Q''
--   R'' : Λ
--   R'' = proj₁ hi
--   P''⇉R'' : P'' ⇉ R''
--   P''⇉R'' = proj₁ (proj₂ hi)
--   Q''⇉R'' : Q'' ⇉ R''
--   Q''⇉R'' = proj₂ (proj₂ hi)
--   P'[y≔P'']⇉（yu）R'[y≔R''] : P' [ y ≔ P'' ] ⇉ (（ y ∙ u ） R') [ y ≔ R'' ]
--   P'[y≔P'']⇉（yu）R'[y≔R''] = lemma⇉Subst y P'  P'⇉（yu）R' P''⇉R''
--   Q'[z≔Q'']⇉（zu）R'[z≔R''] : Q' [ z ≔ Q'' ] ⇉ (（ z ∙ u ） R') [ z ≔ R'' ]
--   Q'[z≔Q'']⇉（zu）R'[z≔R''] = lemma⇉Subst z Q'  Q'⇉（zu）R' Q''⇉R''
--   （yu）R'[y≔R'']∼R'[u≔R''] : (（ y ∙ u ） R') [ y ≔ R'' ] ∼α R' [ u ≔ R'' ]
--   （yu）R'[y≔R'']∼R'[u≔R''] = lemmaSwapSubstVar y u  R'' R' (lemma⇉# y#（yu）P' （yu）P'⇉R')
--   （zu）R'[z≔R'']∼R'[u≔R''] : (（ z ∙ u ） R') [ z ≔ R'' ] ∼α R' [ u ≔ R'' ]
--   （zu）R'[z≔R'']∼R'[u≔R''] = lemmaSwapSubstVar z u  R'' R' (lemma⇉# z#（zu）Q' （zu）Q'⇉R')
-- diam⇉  {M · M'} {N · N'} {P · P'} (⇉· M⇉N M'⇉N') (⇉· M⇉P M'⇉P')
--   = Q · R , ⇉· N⇉Q  N'⇉R , ⇉· P⇉Q P'⇉R 
--   where
--   hi1 : ∃ (λ Q → N ⇉ Q × P ⇉ Q)
--   hi1 = diam⇉ M⇉N M⇉P
--   Q : Λ
--   Q = proj₁ hi1
--   N⇉Q : N ⇉ Q
--   N⇉Q = proj₁ (proj₂ hi1)
--   P⇉Q : P ⇉ Q
--   P⇉Q = proj₂ (proj₂ hi1)
--   hi2 : ∃ (λ R → N' ⇉ R × P' ⇉ R)
--   hi2 = diam⇉ M'⇉N' M'⇉P'
--   R : Λ
--   R = proj₁ hi2
--   N'⇉R : N' ⇉ R
--   N'⇉R = proj₁ (proj₂ hi2)
--   P'⇉R : P' ⇉ R
--   P'⇉R = proj₂ (proj₂ hi2)
-- diam⇉  {ƛ x M · N} {P} {ƛ z Q' · Q''} 
--        (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
--        (⇉· ƛxM⇉λzQ' N⇉Q'') 
--   =  R' [ u ≔ R'' ]               ,
--      P⇉R'[u≔R'']                  ,
--      ⇉β z u ƛzQ'⇉ƛuR' Q''⇉R'' ρ
--   where
--   hi : ∃ (λ R → P'' ⇉ R × Q'' ⇉ R)
--   hi  = diam⇉ N⇉P'' N⇉Q''
--   R'' : Λ
--   R'' = proj₁ hi
--   P''⇉R'' : P'' ⇉ R''
--   P''⇉R'' = proj₁ (proj₂ hi)
--   Q''⇉R'' : Q'' ⇉ R''
--   Q''⇉R'' = proj₂ (proj₂ hi)
--   hi2 : ∃ (λ R → ƛ y P' ⇉ R × ƛ z Q' ⇉ R)
--   hi2 = diam⇉ ƛxM⇉λyP' ƛxM⇉λzQ'
--   R : Λ
--   R = proj₁ hi2
--   u : Atom
--   u = proj₁ (lemma⇉ƛ (proj₁ (proj₂ hi2)))
--   R' : Λ
--   R' = proj₁ (proj₂ (lemma⇉ƛ (proj₁ (proj₂ hi2))))
--   us : List Atom
--   us = proj₁ (proj₂ (proj₂ (lemma⇉ƛ (proj₁ (proj₂ hi2)))))
--   R≡ƛuR' : R ≡ ƛ u R'
--   R≡ƛuR' = proj₁ (proj₂ (proj₂ (proj₂ (lemma⇉ƛ (proj₁ (proj₂ hi2))))))
--   ∀w∉us→（yw）P'⇉（uw）R' : (w : Atom) → w ∉ us → （ y ∙ w ） P' ⇉ （ u ∙ w ） R'
--   ∀w∉us→（yw）P'⇉（uw）R' = proj₂ (proj₂ (proj₂ (proj₂ (lemma⇉ƛ (proj₁ (proj₂ hi2))))))
--   w = χ' (us ++ fv R')
--   w∉ = χ'∉ (us ++ fv R')
--   w∉us : w ∉ us
--   w∉us = c∉xs++ys→c∉xs w∉
--   w#R' : w # R'
--   w#R' = lemma∉fv→# (c∉xs++ys→c∉ys {xs = us} w∉)
--   ƛyP'⇉ƛuR' : ƛ y P' ⇉ ƛ u R'
--   ƛyP'⇉ƛuR' = subst (λ H → ƛ y P' ⇉ H) R≡ƛuR' (proj₁ (proj₂ hi2))
--   y#ƛuR' : y # ƛ u R'
--   y#ƛuR' = lemma⇉# #ƛ≡ ƛyP'⇉ƛuR'
--   （yw）（uw）R'∼（uy）R' : （ y ∙ w ） (（ u ∙ w ） R') ∼α （ u ∙ y ） R'
--   （yw）（uw）R'∼（uy）R'
--     =  begin
--          （ y ∙ w ） （ u ∙ w ） R'
--        ≈⟨ lemma∙comm ⟩
--          （ w ∙ y ） （ u ∙ w ） R'
--        ∼⟨ lemma∙cancel∼α' y#ƛuR' w#R' ⟩
--          （ u ∙ y ） R'
--        ∎        
--   P'⇉（uy）R' : P' ⇉ （ u ∙ y ） R'
--   P'⇉（uy）R' = lemma⇉αright (subst (λ H → H ⇉ （ y ∙ w ） （ u ∙ w ） R') (lemma（ab）（ab）M≡M {y} {w} {P'}) (lemma⇉Equiv [ (y , w) ] (∀w∉us→（yw）P'⇉（uw）R' w w∉us))) （yw）（uw）R'∼（uy）R'
--   ƛzQ'⇉ƛuR' : ƛ z Q' ⇉ ƛ u R'
--   ƛzQ'⇉ƛuR' = subst (λ H → ƛ z Q' ⇉ H) R≡ƛuR' (proj₂ (proj₂ hi2))
--   P'[y≔P'']⇉（uy）R'[y≔R''] : P' [ y ≔ P'' ] ⇉ (（ y ∙ u ） R' ) [ y ≔ R'' ]
--   P'[y≔P'']⇉（uy）R'[y≔R''] = subst (λ H → P' [ y ≔ P'' ] ⇉ H [ y ≔ R'' ]) (lemma∙comm {u} {y} {R'}) (lemma⇉Subst y P' P'⇉（uy）R' P''⇉R'')
--   P⇉R'[u≔R''] : P ⇉ R' [ u ≔ R'' ]
--   P⇉R'[u≔R''] = lemma⇉αright (lemma⇉αleft (σ P'[y≔P'']∼P) P'[y≔P'']⇉（uy）R'[y≔R'']) (lemmaSwapSubstVar' y u R'' R' y#ƛuR')
-- diam⇉  {ƛ x M · N} {ƛ z Q' · Q''} {P}
--        (⇉· ƛxM⇉λzQ' N⇉Q'') 
--        (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
--   =  R' [ u ≔ R'' ]               ,
--      ⇉β z u ƛzQ'⇉ƛuR' Q''⇉R'' ρ   ,
--      P⇉R'[u≔R'']
--   where
--   hi : ∃ (λ R → P'' ⇉ R × Q'' ⇉ R)
--   hi  = diam⇉ N⇉P'' N⇉Q''
--   R'' : Λ
--   R'' = proj₁ hi
--   P''⇉R'' : P'' ⇉ R''
--   P''⇉R'' = proj₁ (proj₂ hi)
--   Q''⇉R'' : Q'' ⇉ R''
--   Q''⇉R'' = proj₂ (proj₂ hi)
--   hi2 : ∃ (λ R → ƛ y P' ⇉ R × ƛ z Q' ⇉ R)
--   hi2 = diam⇉ ƛxM⇉λyP' ƛxM⇉λzQ'
--   R : Λ
--   R = proj₁ hi2
--   u : Atom
--   u = proj₁ (lemma⇉ƛ (proj₁ (proj₂ hi2)))
--   R' : Λ
--   R' = proj₁ (proj₂ (lemma⇉ƛ (proj₁ (proj₂ hi2))))
--   us : List Atom
--   us = proj₁ (proj₂ (proj₂ (lemma⇉ƛ (proj₁ (proj₂ hi2)))))
--   R≡ƛuR' : R ≡ ƛ u R'
--   R≡ƛuR' = proj₁ (proj₂ (proj₂ (proj₂ (lemma⇉ƛ (proj₁ (proj₂ hi2))))))
--   ∀w∉us→（yw）P'⇉（uw）R' : (w : Atom) → w ∉ us → （ y ∙ w ） P' ⇉ （ u ∙ w ） R'
--   ∀w∉us→（yw）P'⇉（uw）R' = proj₂ (proj₂ (proj₂ (proj₂ (lemma⇉ƛ (proj₁ (proj₂ hi2))))))
--   w = χ' (us ++ fv R')
--   w∉ = χ'∉ (us ++ fv R')
--   w∉us : w ∉ us
--   w∉us = c∉xs++ys→c∉xs w∉
--   w#R' : w # R'
--   w#R' = lemma∉fv→# (c∉xs++ys→c∉ys {xs = us} w∉)
--   ƛyP'⇉ƛuR' : ƛ y P' ⇉ ƛ u R'
--   ƛyP'⇉ƛuR' = subst (λ H → ƛ y P' ⇉ H) R≡ƛuR' (proj₁ (proj₂ hi2))
--   y#ƛuR' : y # ƛ u R'
--   y#ƛuR' = lemma⇉# #ƛ≡ ƛyP'⇉ƛuR'
--   （yw）（uw）R'∼（uy）R' : （ y ∙ w ） (（ u ∙ w ） R') ∼α （ u ∙ y ） R'
--   （yw）（uw）R'∼（uy）R'
--     =  begin
--          （ y ∙ w ） （ u ∙ w ） R'
--        ≈⟨ lemma∙comm ⟩
--          （ w ∙ y ） （ u ∙ w ） R'
--        ∼⟨ lemma∙cancel∼α' y#ƛuR' w#R' ⟩
--          （ u ∙ y ） R'
--        ∎        
--   P'⇉（uy）R' : P' ⇉ （ u ∙ y ） R'
--   P'⇉（uy）R' = lemma⇉αright (subst (λ H → H ⇉ （ y ∙ w ） （ u ∙ w ） R') (lemma（ab）（ab）M≡M {y} {w} {P'}) (lemma⇉Equiv [ (y , w) ] (∀w∉us→（yw）P'⇉（uw）R' w w∉us))) （yw）（uw）R'∼（uy）R'
--   ƛzQ'⇉ƛuR' : ƛ z Q' ⇉ ƛ u R'
--   ƛzQ'⇉ƛuR' = subst (λ H → ƛ z Q' ⇉ H) R≡ƛuR' (proj₂ (proj₂ hi2))
--   P'[y≔P'']⇉（uy）R'[y≔R''] : P' [ y ≔ P'' ] ⇉ (（ y ∙ u ） R' ) [ y ≔ R'' ]
--   P'[y≔P'']⇉（uy）R'[y≔R''] = subst (λ H → P' [ y ≔ P'' ] ⇉ H [ y ≔ R'' ]) (lemma∙comm {u} {y} {R'}) (lemma⇉Subst y P' P'⇉（uy）R' P''⇉R'')
--   P⇉R'[u≔R''] : P ⇉ R' [ u ≔ R'' ]
--   P⇉R'[u≔R''] = lemma⇉αright (lemma⇉αleft (σ P'[y≔P'']∼P) P'[y≔P'']⇉（uy）R'[y≔R'']) (lemmaSwapSubstVar' y u R'' R' y#ƛuR')
-- diam⇉  {ƛ x M · N} {P} {v _ · Q''} 
--        (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
--        (⇉· () N⇉Q'') 
-- diam⇉  {ƛ x M · N} {P} {(_ · _) · Q''} 
--        (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
--        (⇉· () N⇉Q'') 
-- diam⇉  {ƛ x M · N} {v _ · Q''} {P}
--        (⇉· () N⇉Q'') 
--        (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
-- diam⇉  {ƛ x M · N} {(_ · _) · Q''} {P}
--        (⇉· () N⇉Q'') 
--        (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
\end{code}

\begin{code}
diam⇉ :  {M N P : Λ} → M ⇉ N → M ⇉ P
         → ∃ (λ Q → N ⇉ Q × P ⇉ Q)
diam⇉  (⇉v x) (⇉v .x)
  = v x , ⇉v x , ⇉v x
diam⇉  {M · M'} {N · N'} {P · P'} 
       (⇉· M⇉N M'⇉N') (⇉· M⇉P M'⇉P')
  = Q · R , ⇉· N⇉Q  N'⇉R , ⇉· P⇉Q P'⇉R
    where
  hi1 : ∃ (λ Q → N ⇉ Q × P ⇉ Q)
  hi1 = diam⇉ M⇉N M⇉P
  Q : Λ
  Q = proj₁ hi1
  N⇉Q : N ⇉ Q
  N⇉Q = proj₁ (proj₂ hi1)
  P⇉Q : P ⇉ Q
  P⇉Q = proj₂ (proj₂ hi1)
  hi2 : ∃ (λ R → N' ⇉ R × P' ⇉ R)
  hi2 = diam⇉ M'⇉N' M'⇉P'
  R : Λ
  R = proj₁ hi2
  N'⇉R : N' ⇉ R
  N'⇉R = proj₁ (proj₂ hi2)
  P'⇉R : P' ⇉ R
  P'⇉R = proj₂ (proj₂ hi2)
diam⇉  {ƛ x M} {ƛ y N} {ƛ z P} 
       (⇉ƛ xs fxs) (⇉ƛ ys fys)
  with  lemma⇉ƛrule (⇉ƛ xs fxs) 
     |  lemma⇉ƛrule (⇉ƛ ys fys)
...  |  N' , M⇉N' , _ , ƛyN~ƛxN' 
     |  P' , M⇉P' , _ , ƛzP~ƛxP'
  with  diam⇉ M⇉N' M⇉P'
...  |  Q , N'⇉Q , P'⇉Q
  = ƛ x Q , lemma⇉αleft ƛyN~ƛxN' (lemma⇉ƛpres N'⇉Q) , lemma⇉αleft ƛzP~ƛxP' (lemma⇉ƛpres P'⇉Q)
diam⇉  {ƛ x M · N} {P} {Q} 
       (⇉β .{M} {P'} .{N} {P''} .x y (⇉ƛ xs fxs) N⇉P'' P'[y≔P'']∼P) 
       (⇉β .{M} {Q'} .{N} {Q''} .x z (⇉ƛ ys fys) N⇉Q'' Q'[z≔Q'']∼Q)
  with  lemma⇉βrule x y (⇉ƛ xs fxs) N⇉P'' P'[y≔P'']∼P
     |  lemma⇉βrule x z (⇉ƛ ys fys) N⇉Q'' Q'[z≔Q'']∼Q  
...  |  P‴ , ƛxM⇉ƛxP‴ , M‴[x≔P'']~P
     |  Q‴ , ƛxM⇉ƛxQ‴ , Q‴[x≔P'']~Q
  with  diam⇉ ƛxM⇉ƛxP‴ ƛxM⇉ƛxQ‴
     |  diam⇉  N⇉P'' N⇉Q''
...  |  R , ƛxP‴⇉R , ƛxQ‴⇉R
     |  S , P''⇉S  , Q''⇉S
  with  lemma⇉ƛrule ƛxP‴⇉R
     |  lemma⇉ƛrule ƛxQ‴⇉R
...  |  R' , P‴⇉R' , ƛxP‴⇉ƛxR' , R~ƛxR'
     |  R″ , Q‴⇉R″ , ƛxQ‴⇉ƛxR″ , R~ƛxR″ 
  with  lemma∼αƛ← (τ (σ R~ƛxR') R~ƛxR″)
...  |  R'∼R″ 
  =  R' [ x ≔ S ]                                                 , 
     lemma⇉αleft (σ M‴[x≔P'']~P) (lemma⇉Subst x P‴ P‴⇉R' P''⇉S )  , 
     lemma⇉αleft (σ Q‴[x≔P'']~Q) (lemma⇉Subst x Q‴ (lemma⇉αright Q‴⇉R″ (σ R'∼R″)) Q''⇉S ) 
diam⇉  {ƛ x M · N} {P} {ƛ z Q' · Q''} 
       (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
       (⇉· ƛxM⇉λzQ' N⇉Q'') 
  with  lemma⇉βrule x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P
     |  lemma⇉ƛrule ƛxM⇉λzQ'
...  |  P‴ , ƛxM⇉ƛxP‴ , P‴[x≔P'']~P
     |  Q‴ , M⇉Q‴ , ƛxM⇉ƛxQ‴ , ƛzQ'~ƛxQ‴
  with  diam⇉ ƛxM⇉ƛxP‴ ƛxM⇉ƛxQ‴
     |  diam⇉ N⇉P'' N⇉Q''
...  |  Q , ƛxP‴⇉Q , ƛxQ‴⇉Q
     |  R , P''⇉R  , Q''⇉R
  with  lemma⇉ƛrule ƛxP‴⇉Q
     |  lemma⇉ƛrule ƛxQ‴⇉Q
...  |  S' , P‴⇉S' , ƛxP‴⇉ƛxS' , Q~ƛxS'
     |  S″ , Q‴⇉S″ , ƛxQ‴⇉ƛxS″ , Q~ƛxS″ 
  with  lemma∼αƛ← (τ (σ Q~ƛxS') Q~ƛxS″)
...  |  S'∼S″ 
  =  S' [ x ≔ R ]                                                  ,
     lemma⇉αleft  (σ P‴[x≔P'']~P) (lemma⇉Subst x P‴ P‴⇉S' P''⇉R)   ,
     lemma⇉αleft  (∼α· ƛzQ'~ƛxQ‴ ρ) 
                  (⇉β x x (lemma⇉αright ƛxQ‴⇉ƛxS″ (lemma∼αƛ (σ S'∼S″))) Q''⇉R ρ) 
diam⇉  {ƛ x M · N} {ƛ z Q' · Q''} {P}
       (⇉· ƛxM⇉λzQ' N⇉Q'') 
       (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
  with  lemma⇉βrule x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P
     |  lemma⇉ƛrule ƛxM⇉λzQ'
...  |  P‴ , ƛxM⇉ƛxP‴ , P‴[x≔P'']~P
     |  Q‴ , M⇉Q‴ , ƛxM⇉ƛxQ‴ , ƛzQ'~ƛxQ‴
  with  diam⇉ ƛxM⇉ƛxP‴ ƛxM⇉ƛxQ‴
     |  diam⇉ N⇉P'' N⇉Q''
...  |  Q , ƛxP‴⇉Q , ƛxQ‴⇉Q
     |  R , P''⇉R  , Q''⇉R
  with  lemma⇉ƛrule ƛxP‴⇉Q
     |  lemma⇉ƛrule ƛxQ‴⇉Q
...  |  S' , P‴⇉S' , ƛxP‴⇉ƛxS' , Q~ƛxS'
     |  S″ , Q‴⇉S″ , ƛxQ‴⇉ƛxS″ , Q~ƛxS″ 
  with  lemma∼αƛ← (τ (σ Q~ƛxS') Q~ƛxS″)
...  |  S'∼S″ 
  =  S' [ x ≔ R ]                                                                 ,
     lemma⇉αleft  (∼α· ƛzQ'~ƛxQ‴ ρ) 
                  (⇉β x x (lemma⇉αright ƛxQ‴⇉ƛxS″ (lemma∼αƛ (σ S'∼S″))) Q''⇉R ρ)  ,
     lemma⇉αleft  (σ P‴[x≔P'']~P) (lemma⇉Subst x P‴ P‴⇉S' P''⇉R)   
diam⇉  {ƛ x M · N} {P} {v _ · Q''} 
       (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
       (⇉· () N⇉Q'') 
diam⇉  {ƛ x M · N} {P} {(_ · _) · Q''} 
       (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
       (⇉· () N⇉Q'') 
diam⇉  {ƛ x M · N} {v _ · Q''} {P}
       (⇉· () N⇉Q'') 
       (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P) 
diam⇉  {ƛ x M · N} {(_ · _) · Q''} {P}
       (⇉· () N⇉Q'') 
       (⇉β .{M} {P'} .{N} {P''} .{P} .x y ƛxM⇉λyP' N⇉P'' P'[y≔P'']∼P)
\end{code}
