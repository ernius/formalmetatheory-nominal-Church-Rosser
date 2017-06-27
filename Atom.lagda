\begin{code}
module Atom where

open import Data.Nat
open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Sum
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)

Atom = ℕ
--
_≟ₐ_ = _≟_
--
\end{code}

%<*swap>
\begin{code}
（_∙_）ₐ_ : Atom → Atom → Atom → Atom
（ a ∙ b ）ₐ c  with c ≟ₐ a
... | yes  _             = b
... | no   _   with c ≟ₐ b
...            |  yes _  = a
...            |  no  _  = c
\end{code}
%</swap>

\begin{code}
sym≢ : {a b : Atom} → a ≢ b → b ≢ a
sym≢ a≢b b≡a = ⊥-elim (a≢b (sym b≡a))
--
lemma∙ₐ :  ∀ a b c →
           (c ≡ a ∧           （ a ∙ b ）ₐ c ≡ b)  ∨ 
           (c ≡ b ∧  c ≢ a ∧  （ a ∙ b ）ₐ c ≡ a)  ∨ 
           (c ≢ a ∧  c ≢ b ∧  （ a ∙ b ）ₐ c ≡ c)
lemma∙ₐ a b c with c ≟ₐ a 
... | yes  c≡a = inj₁ (c≡a , refl)
... | no   c≢a with c ≟ₐ b
...            | yes  c≡b = inj₂ (inj₁ (c≡b , c≢a , refl)) 
...            | no   c≢b = inj₂ (inj₂ (c≢a , c≢b , refl))  
--
lemma∙ₐc≡a :  ∀ a b c → c ≡ a → （ a ∙ b ）ₐ c ≡ b
lemma∙ₐc≡a a b c c≡a with （ a ∙ b ）ₐ c | lemma∙ₐ a b c
lemma∙ₐc≡a a  b  .a  c≡a | .b | inj₁ (refl , refl)               = refl 
lemma∙ₐc≡a a  b  .b  c≡a | .a | inj₂ (inj₁ (refl , c≢a , refl))  = ⊥-elim (c≢a c≡a)
lemma∙ₐc≡a a  b  c   c≡a | .c | inj₂ (inj₂ (c≢a  , c≢b , refl))  = ⊥-elim (c≢a c≡a)
--
lemma∙ₐc≡b :  ∀ a b c → c ≡ b → （ a ∙ b ）ₐ c ≡ a
lemma∙ₐc≡b a b c c≡b with （ a ∙ b ）ₐ c | lemma∙ₐ a b c
lemma∙ₐc≡b a  b  .a  c≡b | .b | inj₁ (refl , refl)                = sym c≡b
lemma∙ₐc≡b a  b  .b  c≡b | .a | inj₂ (inj₁ (refl  , _ , refl))    = refl
lemma∙ₐc≡b a  b  c   c≡b | .c | inj₂ (inj₂ (_     , c≢b , refl))  = ⊥-elim (c≢b c≡b)
--
lemma∙ₐc≢a∧c≢b :  ∀ {a b c} → c ≢ a → c ≢ b → （ a ∙ b ）ₐ c ≡ c
lemma∙ₐc≢a∧c≢b {a} {b} {c}   c≢a c≢b with （ a ∙ b ）ₐ c | lemma∙ₐ a b c
lemma∙ₐc≢a∧c≢b {a} {b} {.a}  c≢a c≢b | .b | inj₁ (refl , refl)              = ⊥-elim (c≢a refl) 
lemma∙ₐc≢a∧c≢b {a} {b} {.b}  c≢a c≢b | .a | inj₂ (inj₁ (refl  , _ , refl))  = ⊥-elim (c≢b refl) 
lemma∙ₐc≢a∧c≢b {a} {b} {c}   c≢a c≢b | .c | inj₂ (inj₂ (_     , _ , refl))  = refl
--
lemma∙ₐa≢b∧a≢c∧a≢d→a≢（bc）d :  ∀ {a b c d} → a ≢ b → a ≢ c → a ≢ d → a ≢ （ b ∙ c ）ₐ d
lemma∙ₐa≢b∧a≢c∧a≢d→a≢（bc）d {a} {b} {c} {d} a≢b a≢c a≢d with （ b ∙ c ）ₐ d | lemma∙ₐ b c d
lemma∙ₐa≢b∧a≢c∧a≢d→a≢（bc）d {a} {b} {c} .{b} a≢b a≢c a≢d | .c | inj₁ (refl , refl)              = a≢c
lemma∙ₐa≢b∧a≢c∧a≢d→a≢（bc）d {a} {b} {c} .{c} a≢b a≢c a≢d | .b | inj₂ (inj₁ (refl  , _ , refl))  = a≢b
lemma∙ₐa≢b∧a≢c∧a≢d→a≢（bc）d {a} {b} {c} {d} a≢b a≢c a≢d  | .d | inj₂ (inj₂ (_     , _ , refl))  = a≢d
--
lemma（aa）b≡b : ∀ {a} {b} → （ a ∙ a ）ₐ b ≡ b
lemma（aa）b≡b {a}   {b} with （ a ∙ a ）ₐ b | lemma∙ₐ a a b
lemma（aa）b≡b {.b}  {b} | .b | inj₁ (refl , refl)          = refl
lemma（aa）b≡b {.b}  {b} | .b | inj₂ (inj₁ (refl  , _ , refl))   = refl
lemma（aa）b≡b {a}   {b} | .b | inj₂ (inj₂ (_     , _ , refl))  = refl

\end{code}

%<*idempotent>
\begin{code}
lemma（ab）（ab）c≡c  : {a b c : Atom} 
                     → （ a ∙ b ）ₐ （ a ∙ b ）ₐ c ≡ c
\end{code}
%</idempotent>

\begin{code}
lemma（ab）（ab）c≡c {a} {b} {c} with （ a ∙ b ）ₐ c | lemma∙ₐ a b c
lemma（ab）（ab）c≡c {a} {b} {.a}  | .b | inj₁ (refl , refl)              = lemma∙ₐc≡b a b b refl
lemma（ab）（ab）c≡c {a} {b} {.b}  | .a | inj₂ (inj₁ (refl , _ , refl))   = lemma∙ₐc≡a a b a refl  
lemma（ab）（ab）c≡c {a} {b} {c}   | .c | inj₂ (inj₂ (c≢a , c≢b , refl))  = lemma∙ₐc≢a∧c≢b c≢a c≢b 
\end{code}

%<*injective>
\begin{code}
lemma∙ₐinj  : {a b c d : Atom} 
            → c ≢ d 
            → （ a ∙ b ）ₐ c ≢ （ a ∙ b ）ₐ d
\end{code}
%</injective>

\begin{code}
lemma∙ₐinj {a} {b} {c} {d} c≢d （ab）c≡（ab）d 
           = ⊥-elim (c≢d (  begin≡ 
                              c 
                            ≡⟨ sym lemma（ab）（ab）c≡c ⟩
                              （ a ∙ b ）ₐ （ a ∙ b ）ₐ c
                            ≡⟨  cong (（_∙_）ₐ_ a b) （ab）c≡（ab）d  ⟩
                              （ a ∙ b ）ₐ （ a ∙ b ）ₐ d
                            ≡⟨ lemma（ab）（ab）c≡c ⟩
                             d
                            □))
--
lemma∙ₐcomm : ∀ {a} {b} {c} → （ a ∙ b ）ₐ c ≡ （ b ∙ a ）ₐ c
lemma∙ₐcomm {a} {b} {c}   with （ a ∙ b ）ₐ c | lemma∙ₐ a b c
lemma∙ₐcomm {a} {b} {.a}  | .b | inj₁ (refl , refl)               = sym (lemma∙ₐc≡b b a a refl)              
lemma∙ₐcomm {a} {b} {.b}  | .a | inj₂ (inj₁ (refl , c≢a , refl))  = sym (lemma∙ₐc≡a b a b refl)              
lemma∙ₐcomm {a} {b} {c}   | .c | inj₂ (inj₂ (c≢a  , c≢b , refl))  = sym (lemma∙ₐc≢a∧c≢b c≢b c≢a) 
--
lemma∙ₐ（aa）a≡a : ∀ {a} → （ a ∙ a ）ₐ a ≡ a 
lemma∙ₐ（aa）a≡a {a} = lemma∙ₐc≡a a a a refl
--
lemma∙ₐ（ab）a≡b : ∀ {a} {b} → （ a ∙ b ）ₐ a ≡ b 
lemma∙ₐ（ab）a≡b {a} {b} = lemma∙ₐc≡a a b a refl
--
lemma∙ₐ（ab）b≡a : ∀ {a} {b} → （ a ∙ b ）ₐ b ≡ a
lemma∙ₐ（ab）b≡a {a} {b} = lemma∙ₐc≡b a b b refl
--
lemma∙ₐdistributive : ∀ a b c d e →
  （ a ∙ b ）ₐ （ c ∙ d ）ₐ e ≡ （ （ a ∙ b ）ₐ c ∙ （ a ∙ b ）ₐ d ）ₐ （ a ∙ b ）ₐ e
lemma∙ₐdistributive a b c d e with （ c ∙ d ）ₐ e | lemma∙ₐ c d e
lemma∙ₐdistributive a  b  c  d  .c | .d | inj₁ (refl , refl)               
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d
lemma∙ₐdistributive a  b  c  .a .c | .a | inj₁ (refl , refl) | .b  | inj₁ (refl , refl)              
  with （ a ∙ b ）ₐ c | lemma∙ₐ a b c 
lemma∙ₐdistributive a  b  .a  .a .a | .a | inj₁ (refl , refl) | .b  | inj₁ (refl , refl) | .b  | inj₁ (refl , refl)                           
  = sym lemma∙ₐ（aa）a≡a
lemma∙ₐdistributive a  b  .b .a .b  | .a | inj₁ (refl , refl) | .b  | inj₁ (refl , refl) | .a  | inj₂ (inj₁ (refl , c≢a , refl))
  = sym (lemma∙ₐ（ab）a≡b {a} {b})
lemma∙ₐdistributive a  b  c  .a .c  | .a | inj₁ (refl , refl) | .b  | inj₁ (refl , refl) | .c  | inj₂ (inj₂ (c≢a , c≢b , refl))                         = sym (lemma∙ₐ（ab）a≡b {c} {b})
lemma∙ₐdistributive a  b  c  .b .c  | .b | inj₁ (refl , refl) | .a  | inj₂ (inj₁ (refl , d≢a , refl))               
  with （ a ∙ b ）ₐ c | lemma∙ₐ a b c 
lemma∙ₐdistributive a  b  .a  .b .a | .b | inj₁ (refl , refl) | .a  | inj₂ (inj₁ (refl , d≢a , refl))  | .b | inj₁ (refl , refl)              
  = sym (lemma∙ₐ（ab）a≡b {b} {a})
lemma∙ₐdistributive a  b  .b  .b .b | .b | inj₁ (refl , refl) | .a  | inj₂ (inj₁ (refl , d≢a , refl))  | .a | inj₂ (inj₁ (refl , c≢a , refl))
  = sym (lemma∙ₐ（aa）a≡a {a})
lemma∙ₐdistributive a  b  c  .b .c  | .b | inj₁ (refl , refl) | .a  | inj₂ (inj₁ (refl , d≢a , refl))  | .c | inj₂ (inj₂ (c≢a , c≢b , refl))
  = sym (lemma∙ₐ（ab）a≡b {c} {a})
lemma∙ₐdistributive a  b  c  d  .c  | .d | inj₁ (refl , refl) | .d  | inj₂ (inj₂ (d≢a  , d≢b , refl))               
  with （ a ∙ b ）ₐ c | lemma∙ₐ a b c 
lemma∙ₐdistributive a  b  .a  d  .a | .d | inj₁ (refl , refl) | .d  | inj₂ (inj₂ (d≢a  , d≢b , refl))  | .b | inj₁ (refl , refl)              
  = sym (lemma∙ₐ（ab）a≡b {b} {d})
lemma∙ₐdistributive a  b  .b  d  .b  | .d | inj₁ (refl , refl) | .d  | inj₂ (inj₂ (d≢a  , d≢b , refl)) | .a | inj₂ (inj₁ (refl , c≢a , refl))   
  = sym (lemma∙ₐ（ab）a≡b {a} {d})
lemma∙ₐdistributive a  b  c  d  .c  | .d | inj₁ (refl , refl) | .d  | inj₂ (inj₂ (d≢a  , d≢b , refl))  | .c | inj₂ (inj₂ (c≢a , c≢b , refl))
  = sym (lemma∙ₐ（ab）a≡b {c} {d})
lemma∙ₐdistributive a  b  c  d  .d | .c | inj₂ (inj₁ (refl , d≢c , refl)) 
  with （ a ∙ b ）ₐ c | lemma∙ₐ a b c 
lemma∙ₐdistributive a  b  .a  d  .d | .a | inj₂ (inj₁ (refl , d≢a , refl)) | .b | inj₁ (refl , refl)              
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d 
lemma∙ₐdistributive a  b  .a  d  .d | .a | inj₂ (inj₁ (refl , d≢a , refl)) | .b | inj₁ (refl , refl) | _  | inj₁ (d≡a , _)               
  = ⊥-elim (d≢a d≡a)
lemma∙ₐdistributive a  b  .a  .b  .a | .a | inj₂ (inj₁ (refl , b≢a , refl)) | .b | inj₁ (refl , refl) | .a | inj₂ (inj₁ (refl , _ , refl))
  = sym (lemma∙ₐ（ab）b≡a {b} {a})
lemma∙ₐdistributive a  b  .a  d  .d | .a | inj₂ (inj₁ (refl , d≢a , refl)) | .b | inj₁ (refl , refl) | .d | inj₂ (inj₂ (_ , d≢b , refl))
  = sym (lemma∙ₐ（ab）b≡a {b} {d})
lemma∙ₐdistributive a  b  .b  d  .d | .b | inj₂ (inj₁ (refl , d≢b , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl))   
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d 
lemma∙ₐdistributive a  b  .b  .a  .a | .b | inj₂ (inj₁ (refl , a≢b , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl)) | .b  | inj₁ (refl , refl)
  = sym (lemma∙ₐ（ab）b≡a {a} {b})
lemma∙ₐdistributive a  b  .b  d  .d | .b | inj₂ (inj₁ (refl , d≢b , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl)) | _   | inj₂ (inj₁ (d≡b , _ , _))  
  = ⊥-elim (d≢b d≡b)
lemma∙ₐdistributive a  b  .b  d  .d | .b | inj₂ (inj₁ (refl , d≢b , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl)) | .d | inj₂ (inj₂ (_ , d≢a , refl))  
  = sym (lemma∙ₐ（ab）b≡a {a} {d})
lemma∙ₐdistributive a  b  c  d  .d | .c | inj₂ (inj₁ (refl  , d≢c , refl)) | .c | inj₂ (inj₂ (c≢a , c≢b , refl))
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d 
lemma∙ₐdistributive a  b  c  .a  .a | .c | inj₂ (inj₁ (refl  , a≢c , refl)) | .c | inj₂ (inj₂ (c≢a , c≢b , refl)) | .b  | inj₁ (refl , refl)
  = sym (lemma∙ₐ（ab）b≡a {c} {b})
lemma∙ₐdistributive a  b  c  .b  .b | .c | inj₂ (inj₁ (refl  , b≢c , refl)) | .c | inj₂ (inj₂ (c≢a , c≢b , refl)) | .a   | inj₂ (inj₁ (refl , d≢a , refl))  
  = sym (lemma∙ₐ（ab）b≡a {c} {a})
lemma∙ₐdistributive a  b  c  d  .d | .c | inj₂ (inj₁ (refl  , d≢c , refl)) | .c | inj₂ (inj₂ (c≢a , c≢b , refl)) | .d | inj₂ (inj₂ (d≢b , d≢a , refl))  
  = sym (lemma∙ₐ（ab）b≡a {c} {d})
lemma∙ₐdistributive a  b  c  d  e  | .e | inj₂ (inj₂ (e≢c   , e≢d , refl))
  with （ a ∙ b ）ₐ e | lemma∙ₐ a b e
lemma∙ₐdistributive a  b  c  d  .a  | .a | inj₂ (inj₂ (a≢c   , a≢d , refl)) | .b | inj₁ (refl , refl)
  with （ a ∙ b ）ₐ c | lemma∙ₐ a b c
lemma∙ₐdistributive a  b  c  d  .a  | .a | inj₂ (inj₂ (a≢c   , a≢d , refl)) | .b | inj₁ (refl , refl) | _ | inj₁ (c≡a , _)
  = ⊥-elim (a≢c (sym c≡a))
lemma∙ₐdistributive a  b  .b  d  .a  | .a | inj₂ (inj₂ (a≢b   , a≢d , refl)) | .b | inj₁ (refl , refl) | .a | inj₂ (inj₁ (refl , c≢a , refl))
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d
lemma∙ₐdistributive a  b  .b  d  .a  | .a | inj₂ (inj₂ (a≢b   , a≢d , refl)) | .b | inj₁ (refl , refl) | .a | inj₂ (inj₁ (refl , c≢a , refl))
  | _ | inj₁ (d≡a , _)
  = ⊥-elim (a≢d (sym d≡a))
lemma∙ₐdistributive a  b  .b  .b  .a  | .a | inj₂ (inj₂ (a≢b   , _ , refl)) | .b | inj₁ (refl , refl) | .a | inj₂ (inj₁ (refl , c≢a , refl))
  | .a | inj₂ (inj₁ (refl , d≢a , refl))
  = sym (lemma（aa）b≡b)
lemma∙ₐdistributive a  b  .b  d  .a  | .a | inj₂ (inj₂ (a≢b   , a≢d , refl)) | .b | inj₁ (refl , refl) | .a | inj₂ (inj₁ (refl , c≢a , refl))
  | .d | inj₂ (inj₂ (d≢a , d≢b , refl))
  = sym (lemma∙ₐc≢a∧c≢b (sym≢ a≢b) (sym≢ d≢b))
lemma∙ₐdistributive a  b  c  d  .a  | .a | inj₂ (inj₂ (a≢c   , a≢d , refl)) | .b | inj₁ (refl , refl) | .c | inj₂ (inj₂ (c≢b , c≢a , refl))
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d
lemma∙ₐdistributive a  b  c  d  .a  | .a | inj₂ (inj₂ (a≢c   , a≢d , refl)) | .b | inj₁ (refl , refl) | .c | inj₂ (inj₂ (c≢b , c≢a , refl))
  | _ | inj₁ (d≡a , _)
  = ⊥-elim (a≢d (sym d≡a))
lemma∙ₐdistributive a  b  c  .b  .a  | .a | inj₂ (inj₂ (a≢c   , a≢b , refl)) | .b | inj₁ (refl , refl) | .c | inj₂ (inj₂ (c≢a , c≢b , refl))
  | .a | inj₂ (inj₁ (refl , _ , refl))
  = sym (lemma∙ₐc≢a∧c≢b (sym≢ c≢b) (sym≢ a≢b))
lemma∙ₐdistributive a  b  c  d  .a  | .a | inj₂ (inj₂ (a≢c   , a≢d , refl)) | .b | inj₁ (refl , refl) | .c | inj₂ (inj₂ (c≢a , c≢b , refl))
  | .d | inj₂ (inj₂ (d≢a , d≢b , refl))
  = sym (lemma∙ₐc≢a∧c≢b (sym≢ c≢b) (sym≢ d≢b))
lemma∙ₐdistributive a  b  c  d  .b  | .b | inj₂ (inj₂ (b≢c   , b≢d , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl))
  with （ a ∙ b ）ₐ c | lemma∙ₐ a b c
lemma∙ₐdistributive a  b  .a  d  .b  | .b | inj₂ (inj₂ (_  , b≢d , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl))  | .b | inj₁ (refl , refl)
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d
lemma∙ₐdistributive a  b  .a  .a  .b  | .b | inj₂ (inj₂ (_  , _ , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl))  | .b | inj₁ (refl , refl)
  | .b | inj₁ (refl , refl)
  = sym (lemma（aa）b≡b) 
lemma∙ₐdistributive a  b  .a  d  .b  | .b | inj₂ (inj₂ (_  , b≢d , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl))  | .b | inj₁ (refl , refl)
  | _ | inj₂ (inj₁ (d≡b , _ , _))
  = ⊥-elim (b≢d (sym d≡b))
lemma∙ₐdistributive a  b  .a  d  .b  | .b | inj₂ (inj₂ (_  , b≢d , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl))  | .d | inj₁ (refl , refl)
  | .d | inj₂ (inj₂ (d≢a , d≢b , refl))
  = sym (lemma∙ₐc≢a∧c≢b (sym≢ b≢a) (sym≢ d≢a)) 
lemma∙ₐdistributive a  b  c  d  .b  | .b | inj₂ (inj₂ (b≢c   , b≢d , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl)) | _  | inj₂ (inj₁ (c≡b , _ , _))
  = ⊥-elim (b≢c (sym c≡b))
lemma∙ₐdistributive a  b  c  d  .b  | .b | inj₂ (inj₂ (b≢c   , b≢d , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl)) | .c  |  inj₂ (inj₂ (c≢b , c≢a , refl))
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d
lemma∙ₐdistributive a  b  c  .a  .b  | .b | inj₂ (inj₂ (b≢c   , _ , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl)) | .c  |  inj₂ (inj₂ (c≢a , c≢b , refl)) | .b | inj₁ (refl , refl)
  = sym (lemma∙ₐc≢a∧c≢b (sym≢ c≢a) (sym≢ b≢a))   
lemma∙ₐdistributive a  b  c  d  .b  | .b | inj₂ (inj₂ (b≢c   , b≢d , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl)) | .c  |  inj₂ (inj₂ (c≢b , c≢a , refl)) | _ | inj₂ (inj₁ (d≡b , _)) 
  = ⊥-elim (b≢d (sym d≡b))
lemma∙ₐdistributive a  b  c  d  .b  | .b | inj₂ (inj₂ (b≢c   , b≢d , refl)) | .a | inj₂ (inj₁ (refl , b≢a , refl)) | .c  |  inj₂ (inj₂ (c≢a , c≢b , refl)) | .d | inj₂ (inj₂ (d≢a , d≢b , refl)) 
  = sym (lemma∙ₐc≢a∧c≢b (sym≢ c≢a) (sym≢ d≢a))    
lemma∙ₐdistributive a  b  c  d  e  | .e | inj₂ (inj₂ (e≢c   , e≢d , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  with （ a ∙ b ）ₐ c | lemma∙ₐ a b c
lemma∙ₐdistributive a  b  .a  d  e  | .e | inj₂ (inj₂ (_   , e≢d , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .b | inj₁ (refl , refl) 
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d
lemma∙ₐdistributive a  b  .a  .a  e  | .e | inj₂ (inj₂ (_   , _ , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl)) 
  | .b | inj₁ (refl , refl) | .b | inj₁ (refl , refl) 
  = sym (lemma（aa）b≡b) 
lemma∙ₐdistributive a  b  .a  .b  e  | .e | inj₂ (inj₂ (_   , _ , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .b | inj₁ (refl , refl) | .a | inj₂ (inj₁ (refl , b≢a , refl)) 
  = sym (lemma∙ₐc≢a∧c≢b e≢b e≢a)
lemma∙ₐdistributive a  b  .a  d  e  | .e | inj₂ (inj₂ (_   , e≢d , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .b | inj₁ (refl , refl) | .d | inj₂ (inj₂ (d≢a , d≢b , refl))
  = sym (lemma∙ₐc≢a∧c≢b e≢b e≢d)
lemma∙ₐdistributive a  b  .b  d  e  | .e | inj₂ (inj₂ (_   , e≢d , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .a | inj₂ (inj₁ (refl , c≢a , refl)) 
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d
lemma∙ₐdistributive a  b  .b  .a  e  | .e | inj₂ (inj₂ (_   , _ , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .a | inj₂ (inj₁ (refl , c≢a , refl)) | . b | inj₁ (refl , refl)
  = sym (lemma∙ₐc≢a∧c≢b e≢a e≢b )
lemma∙ₐdistributive a  b  .b  .b  e  | .e | inj₂ (inj₂ (_   , _ , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .a | inj₂ (inj₁ (refl , c≢a , refl)) | .a  | inj₂ (inj₁ (refl , b≢a , refl))
  = sym lemma（aa）b≡b 
lemma∙ₐdistributive a  b  .b  d  e  | .e | inj₂ (inj₂ (_   , e≢d , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .a | inj₂ (inj₁ (refl , c≢a , refl)) | .d  | inj₂ (inj₂ (d≢a , d≢b , refl))
  = sym (lemma∙ₐc≢a∧c≢b e≢a e≢d )
lemma∙ₐdistributive a  b  c  d  e  | .e | inj₂ (inj₂ (e≢c   , e≢d , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .c | inj₂ (inj₂ (c≢a , c≢b , refl))  
  with （ a ∙ b ）ₐ d | lemma∙ₐ a b d
lemma∙ₐdistributive a  b  c  .a  e  | .e | inj₂ (inj₂ (e≢c   , _ , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .c | inj₂ (inj₂ (c≢a , c≢b , refl)) | .b | inj₁ (refl , refl)
  = sym (lemma∙ₐc≢a∧c≢b e≢c e≢b)
lemma∙ₐdistributive a  b  c  .b  e  | .e | inj₂ (inj₂ (e≢c   , _ , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .c | inj₂ (inj₂ (c≢a , c≢b , refl)) | .a | inj₂ (inj₁ (refl , d≢a , refl))
  = sym (lemma∙ₐc≢a∧c≢b e≢c e≢a)
lemma∙ₐdistributive a  b  c  d  e  | .e | inj₂ (inj₂ (e≢c   , e≢d , refl))  | .e | inj₂ (inj₂ (e≢a , e≢b , refl))
  | .c | inj₂ (inj₂ (c≢a , c≢b , refl)) | .d | inj₂ (inj₂ (d≢a , d≢b , refl))
  = sym (lemma∙ₐc≢a∧c≢b e≢c e≢d)
--
lemma∙ₐcancel : {a b c d : Atom} → d ≢ b → d ≢ c → （ c ∙ b ）ₐ （ a ∙ c ）ₐ d ≡ （ a ∙ b ）ₐ d
lemma∙ₐcancel {a} {b} {c} {d} d≢b d≢c 
  with d ≟ₐ a
... | no _ with d ≟ₐ c
...        | yes d≡c                 = ⊥-elim (d≢c d≡c)
...        | no _  with d ≟ₐ c
...                | yes d≡c         = ⊥-elim (d≢c d≡c)
...                | no _ with d ≟ₐ b
...                       | yes d≡b  = ⊥-elim (d≢b d≡b)
...                       | no _     = refl
lemma∙ₐcancel {a} {b} {c} {.a} a≢b a≢c 
    | yes refl with c ≟ₐ c
...            | yes _               = refl
...            | no c≢c              = ⊥-elim (c≢c refl)
\end{code}
