\begin{code}
module TermRecursion where

open import Atom
open import Term 
open import Alpha
open import TermAcc
open import Chi
open import ListProperties
open import TermInduction
open import Permutation

open import Level
open import Data.Nat
open import Data.Nat.Properties
open import Function
open import Data.List 
open import Data.List.Any as Any hiding (map)
open Any.Membership-≡
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)
\end{code}

Iteration principle done using the induction based on swaps (done with primitive recursion).

%<*termIteration>
\begin{code}
ΛIt  : {l : Level}(A : Set l)
    → (Atom → A)
    → (A → A → A)
    → List Atom × (Atom → A → A) 
--    → Σ (List Atom) (λ vs → (a : Atom) → a ∉ vs → A → A)
    → Λ → A
\end{code}
%</termIteration>


%<*termIterationCode>
\begin{code}
ΛIt A hv h· (vs , hƛ) 
    = TermαPrimInd  (λ _ → A) 
                    (λ _ → id) 
                    hv 
                    (λ _ _ → h·) 
                    (vs , (λ _ b _ r → hƛ b r))
\end{code}
%</termIterationCode>


 \begin{code}
Paux : {l : Level}(A : Set l) → (Atom → A) → (A → A → A) → List Atom → (Atom → A → A) → Λ → Π → A
Paux A hv h· vs hƛ M π
  = TermPrimInd
      (λ _ → (π : List (Atom × Atom)) → A)
      (lemmavIndSw {P = λ _ → A} hv)
      (lemma·IndSw (λ _ _ → h·))
      (lemmaƛIndSw {P = λ _ → A}
        (lemmaαƛ (λ _ → A) (λ  _ → id) vs (λ _ b _ f → hƛ b (f []))))
      M π

P : {l : Level}(A : Set l) → (Atom → A) → (A → A → A) → List Atom → (Atom → A → A) → Λ → Set l
P A hv h· vs hƛ M = ∀ π → Paux A hv h· vs hƛ M π ≡ Paux A hv h· vs hƛ (π ∙ M) []
--
aux : {l : Level}(A : Set l)
    → (hv : Atom → A)
    → (h· : A → A → A)
    → (vs : List Atom)
    → (hƛ : Atom → A → A)
    → ∀ M → P A hv h· vs hƛ M
aux A hv h· vs hƛ M π rewrite lemmaxs++[]≡xs π 
    = TermIndPerm (P A hv h· vs hƛ) lemmav lemma· lemmaƛ M π
    where
    lemmav : (a : ℕ) → P A hv h· vs hƛ (v a)
    lemmav a π rewrite lemmaπv {a} {π} = refl
    lemma· :  (M N : Λ) → P A hv h· vs hƛ M → P A hv h· vs hƛ N → P A hv h· vs hƛ (M · N)
    lemma· M N PM PN π rewrite lemmaπ· {M} {N} {π} = cong₂ h· (PM π) (PN π)
    lemmaƛ :  (M : Λ) (b : ℕ) → ((π : List (Atom × Atom)) → P A hv h· vs hƛ (π ∙ M)) 
              → P A hv h· vs hƛ (ƛ b M)
    lemmaƛ M a PMπ π rewrite lemmaπƛ {a} {M} {π} 
      = cong₂ hƛ refl (begin≡
                      Paux A hv h· vs hƛ M ((π ∙ₐ a ,  χ vs (ƛ (π ∙ₐ a) (π ∙ M))) ∷ π)
                    ≡⟨ PMπ [] ((π ∙ₐ a ,  χ vs (ƛ (π ∙ₐ a) (π ∙ M))) ∷ π)  ⟩
                      Paux A hv h· vs hƛ (((π ∙ₐ a ,  χ vs (ƛ (π ∙ₐ a) (π ∙ M))) ∷ π) ∙ M) []
                    ≡⟨  cong  (λ p → Paux A hv h· vs hƛ p [])
                              (sym (lemmaπ∙π′∙M≡π++π′∙M {[ π ∙ₐ a , χ vs (ƛ (π ∙ₐ a) (π ∙ M))]} {π} {M})) ⟩
                      Paux A hv h· vs hƛ ([(π ∙ₐ a ,  χ vs (ƛ (π ∙ₐ a) (π ∙ M)))] ∙ π ∙ M) []
                    ≡⟨ sym (PMπ π [(π ∙ₐ a ,  χ vs (ƛ (π ∙ₐ a) (π ∙ M)))])  ⟩
                      Paux A hv h· vs hƛ (π ∙ M) [(π ∙ₐ a ,  χ vs (ƛ (π ∙ₐ a) (π ∙ M)))]
                   □)
\end{code}


%<*itlambda>
\begin{code}
ΛItƛ  : {l : Level}(A : Set l)
        → (hv : Atom → A)
        → (h· : A → A → A)
        → (vs : List Atom)
        → (hƛ : Atom → A → A)
        → ∀ a M 
        → ΛIt A hv h· (vs , hƛ) (ƛ a M) ≡ 
        hƛ  (χ vs (ƛ a M)) 
            (ΛIt A hv h· (vs , hƛ) ([ a , (χ vs (ƛ a M))] ∙ M))
\end{code}
%</itlambda>

\begin{code}
ΛItƛ A hv h· vs hƛ a M 
       = cong₂ hƛ refl (aux A hv h· vs hƛ M [ a , χ vs (ƛ a M)]) --
\end{code}

%<*iterationStrongCompatible>
\begin{code}
lemmaΛItStrongαCompatible : {l : Level}(A : Set l)
                            → (hv : Atom → A)
                            → (h· : A → A → A)
                            → (vs : List Atom)
                            → (hƛ : Atom → A → A )
                            → (M : Λ) → strong∼αCompatible (ΛIt A hv h· (vs , hƛ)) M 
\end{code}
%</iterationStrongCompatible>

\begin{code}
lemmaΛItStrongαCompatible A hv h· xs hƛ 
    = TermIndPerm (strong∼αCompatible (ΛIt A hv h· (xs , hƛ))) lemmav lemma· lemmaƛ  
    where
    lemmav :  (a : ℕ) → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) (v a)
    lemmav a .(v a) ∼αv = refl
    lemma· :  (M N : Λ)
              → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) M 
              → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) N 
              → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) (M · N)
    lemma· M N PM PN .(M' · N') (∼α· {.M} {M'} {.N} {N'} M∼M' N∼N') 
      = cong₂ h· (PM M' M∼M') (PN N' N∼N')
    lemmaƛ :  (M : Λ) (b : ℕ) 
              → ((π : List (Atom × Atom)) → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) (π ∙ M)) 
              → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) (ƛ b M)
    lemmaƛ M a PπM .(ƛ b N) (∼αƛ {.M} {N} {.a} {b} vs fα) 
      rewrite 
         ΛItƛ A hv h· xs hƛ a M 
      |  ΛItƛ A hv h· xs hƛ b N 
      with χ xs (ƛ a M) | χ xs (ƛ b N) 
      |  χ# xs (ƛ a M) | χ# xs (ƛ b N) 
      |  χ∼α  (ƛ a M) (ƛ b N) xs (∼αƛ {M} {N} {a} {b} vs fα)  
      |  χ' (vs ++ ocurr (M · N)) | lemmaχ∉ (vs ++ ocurr (M · N))
    ... | c | .c | c#λaM | c#λbN | refl | d | d∉vs++ocurrM·N 
      = cong₂ hƛ refl (PπM [(a , c)] (（ b ∙ c ） N) （ac）M∼α（bc）N)
      where
      d∉vs : d ∉ vs
      d∉vs = c∉xs++ys→c∉xs {d} {vs} {ocurr (M · N)} d∉vs++ocurrM·N
      d∉M : d ∉ₜ M
      d∉M = lemmaocurr (c∉xs++ys→c∉xs {d} {ocurr M} {ocurr N} (c∉xs++ys→c∉ys {d} {vs} {ocurr (M · N)} d∉vs++ocurrM·N)) 
      d∉N : d ∉ₜ N
      d∉N = lemmaocurr (c∉xs++ys→c∉ys {d} {ocurr M} {ocurr N} (c∉xs++ys→c∉ys {d} {vs} {ocurr (M · N)} d∉vs++ocurrM·N)) 
      （ac）M∼α（bc）N : （ a ∙ c ） M ∼α （ b ∙ c ） N
      （ac）M∼α（bc）N =  begin
                           （ a ∙ c ） M 
                         ∼⟨ σ (lemma∙ c#λaM d∉M) ⟩
                           （ d ∙ c ） （ a ∙ d ） M 
                         ∼⟨ lemma∼αEquiv [(d , c)] (fα d d∉vs) ⟩
                           （ d ∙ c ） （ b ∙ d ） N
                         ∼⟨ lemma∙ c#λbN d∉N ⟩
                           （ b ∙ c ） N
                         ∎
\end{code}



\begin{code}
lemmaΛItEquiv# : {l : Level}(A : Set l)
    → (hv : Atom → A)
    → (h· : A → A → A)
    → (vs : List Atom)
    → (hƛ : Atom → A → A )
    → (M : Λ)(a b : Atom) 
    → a # M → b # M 
    → ΛIt A hv h· (vs , hƛ) M ≡ ΛIt A hv h· (vs , hƛ) (（ a ∙ b ） M)
lemmaΛItEquiv# A hv h· vs hƛ M a b a#M b#M 
    = lemmaΛItStrongαCompatible A hv h· vs hƛ M (（ a ∙ b ） M) (lemma#∼α a#M b#M)
\end{code}

Example Id

\begin{code}
idΛ : List Atom → Λ → Λ
idΛ vs = ΛIt Λ v _·_ (vs , ƛ)
--
idΛα : {M : Λ}{vs : List Atom} → M ∼α idΛ vs M
idΛα {M} {vs} = TermIndPerm  (λ M → M ∼α idΛ vs M) 
                             (λ _                  → ∼αv) 
                             (λ M N M∼idΛM N∼idΛN  → ∼α· M∼idΛM N∼idΛN) 
                             lemmaƛ 
                             M
       where
       lemmaƛ :  (M : Λ) (a : ℕ) 
              → ((π : List (Atom × Atom)) → π ∙ M ∼α idΛ vs (π ∙ M)) 
              → ƛ a M ∼α idΛ vs (ƛ a M)
       lemmaƛ M a hi 
         rewrite ΛItƛ Λ v _·_ vs ƛ a M
           =  begin
             ƛ a M 
           ∼⟨ lemma∼λχ {a} {vs} {M} ⟩
             ƛ (χ vs (ƛ a M )) (（ a ∙ (χ vs (ƛ a M )) ） M)
           ∼⟨ lemma∼αƛ (hi [ a , χ vs (ƛ a M ) ]) ⟩
           ƛ (χ vs (ƛ a M )) (idΛ vs (（ a ∙ (χ vs (ƛ a M )) ） M))
         ∎  
\end{code}

Term recursion principle

\begin{code}
app : {l : Level}{A : Set l} → (A → A → Λ → Λ → A) → A × Λ → A × Λ → A × Λ
app h· (r , M) (r′ , M′) = h· r r′ M M′ , M · M′
--
abs : {l : Level}{A : Set l} → (Atom → A → Λ → A) → Atom → A × Λ → A × Λ
abs hƛ a (r , M) = hƛ a r M , ƛ a M
\end{code}

%<*termRecursion>
\begin{code}
ΛRec  : {l : Level}(A : Set l)
        → (Atom → A)
        → (A → A → Λ → Λ → A)
        → List Atom × (Atom → A → Λ → A) 
        → Λ → A
\end{code}
%</termRecursion>


\begin{code}
ΛRec A hv h· (xs , hƛ) M = proj₁ (ΛIt (A × Λ) < hv , v > (app h·) (xs , (abs hƛ)) M)
--
ΛRecv  : {l : Level}(A : Set l)
      → (hv : Atom → A)
      → (h· : A → A → Λ → Λ → A)
      → (vs : List Atom)
      → (hƛ : Atom → A → Λ → A)
      → ∀ a
      → ΛRec A hv h· (vs , hƛ) (v a) ≡ hv a
ΛRecv A hv h· vs  hƛ a = refl

ΛRec·  : {l : Level}(A : Set l)
      → (hv : Atom → A)
      → (h· : A → A → Λ → Λ → A)
      → (vs : List Atom)
      → (hƛ : Atom → A → Λ → A)
      → ∀ M N 
      → ΛRec A hv h· (vs , hƛ) (M · N) ≡ 
        proj₁ (app h·  (ΛIt (A × Λ) < hv , v > (app h·) (vs , (abs hƛ)) M) 
                       (ΛIt (A × Λ) < hv , v > (app h·) (vs , (abs hƛ)) N))
ΛRec· A hv h· vs hƛ M N = refl

ΛRecƛ  : {l : Level}(A : Set l)
      → (hv : Atom → A)
      → (h· : A → A → Λ → Λ → A)
      → (vs : List Atom)
      → (hƛ : Atom → A → Λ → A)
      → ∀ a M 
      → ΛRec A hv h· (vs , hƛ) (ƛ a M) ≡ 
        proj₁ (abs hƛ (χ vs (ƛ a M)) (ΛIt (A × Λ) < hv , v > (app h·) (vs , (abs hƛ)) ([ a , (χ vs (ƛ a M))] ∙ M)))
ΛRecƛ A hv h· vs hƛ a M 
     =  begin≡
       ΛRec A hv h· (vs , hƛ) (ƛ a M) 
     ≡⟨ refl ⟩
       proj₁ (ΛIt (A × Λ) < hv , v > (app h·) (vs , (abs hƛ)) (ƛ a M))
     ≡⟨ cong proj₁ (ΛItƛ (A × Λ) < hv , v > (app h·) vs (abs hƛ) a M) ⟩
       proj₁ (abs hƛ (χ vs (ƛ a M)) (ΛIt (A × Λ) < hv , v > (app h·) (vs , (abs hƛ)) ([ a , (χ vs (ƛ a M))] ∙ M)))
     □
--
--αStrongCompatible
lemmaΛRecStrongαCompatible : {l : Level}(A : Set l)
    → (hv : Atom → A)
    → (h· : A → A → Λ → Λ → A)
    → (hƛ : List Atom × (Atom → A → Λ → A) )
    → ∀ M → strong∼αCompatible (ΛRec  A hv h· hƛ) M
lemmaΛRecStrongαCompatible A hv h· (xs , hƛ) M N M∼αN 
  rewrite lemmaΛItStrongαCompatible (A × Λ) < hv , v > (app h·) xs (abs hƛ) M N M∼αN = refl
\end{code}

\begin{code}
lemmaΛRecEquiv# : {l : Level}(A : Set l)
    → (hv : Atom → A)
    → (h· : A → A → Λ → Λ → A)
    → (hƛ : List Atom × (Atom → A → Λ → A) )
    → (M : Λ)(a b : Atom) 
    → a # M → b # M 
    → ΛRec A hv h· hƛ M ≡ ΛRec A hv h· hƛ (（ a ∙ b ） M)
lemmaΛRecEquiv# A hv h· (xs , hƛ) M a b a#M b#M 
  rewrite lemmaΛItEquiv# (A × Λ) < hv , v > (app h·) xs (abs hƛ) M a b a#M b#M = refl
--  
ΛRec2  : {l : Level}(A : Set l)
        → (Atom → A)
        → (A → A → Λ → Λ → A)
        → List Atom × (Atom → A → Λ → A) 
        → Λ → Λ
ΛRec2 A hv h· (xs , hƛ) M = proj₂ (ΛIt (A × Λ) < hv , v > (app h·) (xs , (abs hƛ)) M)
--
ΛRec2Id  : {l : Level}(A : Set l)
      → (hv : Atom → A)
      → (h· : A → A → Λ → Λ → A)
      → (vs : List Atom)
      → (hƛ : Atom → A → Λ → A)
      → ∀ M
      → ΛRec2 A hv h· (vs , hƛ) M ≡ idΛ vs M
ΛRec2Id A hv h· vs hƛ = TermIndPerm  (λ M → ΛRec2 A hv h· (vs , hƛ) M ≡ idΛ vs M)
                                       (λ _ → refl)
                                       (λ M N hiM hiN → cong₂ _·_ hiM hiN)
                                       lemmaƛ
      where
      lemmaƛ :  (M : Λ) (x : ℕ)
                → ((π : List (Atom × Atom)) → ΛRec2 A hv h· (vs , hƛ) (π ∙ M) ≡ idΛ vs (π ∙ M)) 
                →  ΛRec2 A hv h· (vs , hƛ) (ƛ x M) ≡ idΛ vs (ƛ x M)
      lemmaƛ M x hi 
        rewrite  ΛItƛ (A × Λ) < hv , v > (app h·) vs (abs hƛ) x M
        |        ΛItƛ Λ v _·_ vs ƛ x M 
        |        aux (A × Λ) < hv , v > (app h·) vs (abs hƛ) M [ x , χ vs (ƛ x M)]
        = cong (λ N → ƛ (χ vs (ƛ x M)) N) (hi [ x , χ vs (ƛ x M) ])  
--
ΛRec2α  : {l : Level}(A : Set l)
      → (hv : Atom → A)
      → (h· : A → A → Λ → Λ → A)
      → (vs : List Atom)
      → (hƛ : Atom → A → Λ → A)
      → ∀ M
      → M ∼α ΛRec2 A hv h· (vs , hƛ) M 
ΛRec2α A hv h· vs hƛ M
    rewrite ΛRec2Id A hv h· vs hƛ M = idΛα {M} {vs}
\end{code}

\begin{code}
ΛRec·'  : {l : Level}(A : Set l)
      → (hv : Atom → A)
      → (h· : A → A → Λ → Λ → A)
      → (vs : List Atom)
      → (hƛ : Atom → A → Λ → A)
      → ∀ M N 
      → ∃ (λ M' → ∃ (λ N' →  M ∼α M' × N ∼α N'    ×
                             ΛRec A hv h· (vs , hƛ) (M · N) ≡ h· (ΛRec A hv h· (vs , hƛ) M) (ΛRec A hv h· (vs , hƛ) N) M' N'))
ΛRec·' A hv h· vs hƛ M N 
    =   ΛRec2 A hv h· (vs , hƛ) M  ,
        ΛRec2 A hv h· (vs , hƛ) N  ,
        ΛRec2α A hv h· vs hƛ M     ,
        ΛRec2α A hv h· vs hƛ N     ,
        refl
--
ΛRecƛ'  : {l : Level}(A : Set l)
      → (hv : Atom → A)
      → (h· : A → A → Λ → Λ → A)
      → (vs : List Atom)
      → (hƛ : Atom → A → Λ → A)
      → ∀ a M 
      → ∃ (λ N →  （ a ∙ χ vs (ƛ a M) ） M ∼α N     ×
                  ΛRec A hv h· (vs , hƛ) (ƛ a M) ≡ hƛ (χ vs (ƛ a M)) (ΛRec A hv h· (vs , hƛ) (（ a ∙ (χ vs (ƛ a M)) ） M)) N)
ΛRecƛ' A hv h· vs hƛ a M 
    rewrite ΛRecƛ A hv h· vs hƛ a M 
    =  ΛRec2 A hv h· (vs , hƛ) (（ a ∙ χ vs (ƛ a M) ） M)  ,
       ΛRec2α A hv h· vs hƛ (（ a ∙ χ vs (ƛ a M) ） M)     ,
       refl

  -- Another equivalent signature using lemma∼λχ : {a : Atom}{vs : List Atom}{M : Λ} → ƛ a M ∼α ƛ (χ vs (ƛ a M)) (（ a ∙ (χ vs (ƛ a M)) ） M)  
  --     → ∃ (λ N →  ƛ a M ∼α ƛ (χ vs (ƛ a M)) N     ×
  --                 ΛRec A hv h· (vs , hƛ) (ƛ a M) ≡ hƛ (χ vs (ƛ a M)) (ΛRec A hv h· (vs , hƛ) (（ a ∙ (χ vs (ƛ a M)) ） M)) N)
  -- ΛRecƛ' A hv h· vs hƛ a M 
  --   rewrite ΛRecƛ A hv h· vs hƛ a M 
  --   =  ΛRec2 A hv h· (vs , hƛ) (（ a ∙ χ vs (ƛ a M) ） M)  ,
  --      (begin
  --        ƛ a M
  --      ∼⟨ lemma∼λχ {a} {vs} ⟩
  --        ƛ (χ vs (ƛ a M)) (（ a ∙ χ vs (ƛ a M) ） M)
  --      ∼⟨ lemma∼αƛ (ΛRec2α A hv h· vs hƛ (（ a ∙ χ vs (ƛ a M) ） M)) ⟩
  --        ƛ (χ vs (ƛ a M)) (ΛRec2 A hv h· (vs , hƛ) (（ a ∙ χ vs (ƛ a M) ） M))
  --      ∎)                                                  ,
  --      refl 



\end{code}

-- %<*twotermsIteration>
-- \begin{code}
-- Λ2It  : {l : Level}(A : Set l)
--  → (Atom → Atom → A)
--  → (A → A → A → A → A)
--  → List Atom × (Atom → A → Atom → A → A) 
--  → Λ → Λ → A
-- \end{code}
-- %</twotermsIteration>


-- %<*twotermsIterationCode>
-- \begin{code}
-- Λ2It A hv h· (vs , hƛ) 
--   = TermαPrimInd  (λ _ → A) 
--                   (λ _ → id) 
--                   hv 
--                   (λ _ _ → h·) 
--                   (vs , (λ _ b _ r → hƛ b r))
-- \end{code}
-- %</twotermsIterationCode>


