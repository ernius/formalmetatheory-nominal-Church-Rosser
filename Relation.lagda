%include lhs2TeX.fmt
\long\def\ignore#1{}

\begin{document}

\section{Reflexive and Transitve Clousure of a Relation}

\ignore{
\begin{code}
open import Level hiding (zero)
module Relation {l : Level} (A : Set l) where  

  open import Relation.Nullary
  import Relation.Binary as RB
  import Relation.Unary as RU
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) hiding (trans)
\end{code}
}

\ignore{
\begin{code}
  Rel : Set (suc l)
  Rel = RB.Rel A l 
\end{code}

\begin{code}
  Pred : Set (suc l)
  Pred = RU.Pred A l

  infix 2 _preserved-by_
  _preserved-by_ : Pred → Rel → Set l
  P preserved-by R = ∀ {M N : A} → P M → R M N → P N
\end{code}


The dual $R^{\mathit{op}}$ of a relation $R$ is defined by swapping the pairs.

\begin{code}
  dual : Rel → Rel
  dual R m n = R n m

  -- dual-idem : (R : Rel) → dual (dual R) ≡ R
  -- dual-idem R = {! refl!}
\end{code}

Given two relations $R$ and $S$ over $A$ we can take their union.

\begin{code}
  infix 5 _∪_   
  _∪_  : (R S : Rel) → Rel 
  _∪_ R S a b = R a b ⊎ S a b
\end{code}

Binary relations can be pre-ordered by inclusion, $R$ is less than or
equal to $S$ when $a\,R\,b$ implies $a\,S\,b$; as usual we write $R
\subseteq S$. 

\begin{code}
  _⊆_ : Rel → Rel → Set l
  R ⊆ S = RB._⇒_ R S

  refl-⊆ : {R : Rel} → R ⊆ R
  refl-⊆ aRb = aRb

  trans-⊆ : {R S T : Rel} → R ⊆ S → S ⊆ T → R ⊆ T
  trans-⊆ R⊆S S⊆T aRb = S⊆T (R⊆S aRb)
\end{code}
}

The reflexive and transitive closure of a relation is more naturally
introduced by allowing more than one steps in the transitive clause.
Some immediate facts about the transitive closure of an operation is
that it is monotone and idempotent (besides these two properties one
asks that the closure of $R$ contains $R$, but this is immediate from
the definition). From these two properties we prove that $R \subseteq
\transclos S$ implies $\transclos R \subseteq \transclos S$
(alternatively one can proceed by induction on $a\,\transclos R\,b$); it is
straightforward to prove the other

\begin{code}
  data star (⟿ : Rel) : Rel where
    refl : ∀ {a} → star ⟿ a a
    just : ∀ {a b} → ⟿ a b → star ⟿ a b
    trans : ∀ {a b c } → star ⟿ a b → star ⟿ b c → star ⟿ a c

  mon-star : {R S : Rel} → R ⊆ S → star R ⊆ star S
  mon-star R⊆S refl = refl
  mon-star R⊆S (just aRb) = just (R⊆S aRb)
  mon-star R⊆S (trans aR⋆b bR⋆c) 
    = trans (mon-star R⊆S aR⋆b) (mon-star R⊆S bR⋆c)
  
  idem-star : {R : Rel} → star (star R) ⊆ star R
  idem-star refl = refl
  idem-star (just aRb) = aRb
  idem-star (trans aR⋆b bR⋆c) = trans (idem-star aR⋆b) (idem-star bR⋆c)

  trans-⊆-star : {R S : Rel} → R ⊆ star S → star R ⊆ star S
  trans-⊆-star {R} {S} R⊆S⋆ 
    = trans-⊆  {star R} {star (star S)} {star S} 
               (mon-star R⊆S⋆) 
               idem-star
\end{code}

Our next goal is to prove that the diamond property implies
Church-Rosser; for this it turns out that dealing with the usual
definition of the reflexive transitive closure is not convenient,
because the termination checker is not convinced about the use of the
inductive hypothesis in one case. In order to bypass this obstacle we
present another formalisation of the reflexive and transitive closure
of a relation $R^\omega = \bigcup_{n\in \mathbb N} R^n$; although
these two notions are not isomorphic (when passing from $\transclos R$ to
$R^{\omega}$ we lane all the single steps to the left), they are
equivalent.

\begin{code}
  data steps (⟿ : Rel) : Rel where
    zero  : ∀ {a}                               → steps ⟿ a a
    one   : ∀ {a b}    → ⟿ a b                 → steps ⟿ a b
    more  : ∀ {a b c}  → ⟿ a b → steps ⟿ b c  → steps ⟿ a c

  _++_ :  {⟿ : Rel} {a b c : A} 
          → steps ⟿ a b → steps ⟿ b c → steps ⟿ a c
  zero ++ s' = s'
  one a⟿b ++ b⟿*c = more a⟿b b⟿*c
  more a⟿b b⟿*c ++ c⟿*d = more a⟿b (b⟿*c ++ c⟿*d)
  
  ⋆-to-ω : ∀ {a b ⟿} → star ⟿ a b → steps ⟿ a b
  ⋆-to-ω refl = zero
  ⋆-to-ω (just a⟿b) = one a⟿b
  ⋆-to-ω (trans a⟿*b b⟿*c) = ⋆-to-ω a⟿*b ++ ⋆-to-ω b⟿*c

  ω-to-⋆ : ∀ {a b ⟿} → steps ⟿ a b → star ⟿ a b
  ω-to-⋆ zero = refl
  ω-to-⋆ (one a⟿b) = just a⟿b
  ω-to-⋆ (more a⟿b b⟿*c) = trans (just a⟿b) (ω-to-⋆ b⟿*c)
\end{code}

A relation $R$ is said to have the \emph{diamond} property if whenever
$a\,R\,b$ and $a\,R\,c$, there is a $d$ such that $b\,R\,d$ and
$c\,R\,d$; we will say that $R$ is \emph{diamantine} if it satisfies
the diamond property.

\begin{minipage}{0.7\textwidth}
\begin{code}
  diamond : (_⟿_ : Rel) → Set l
  diamond _⟿_ =  {a b c : A} 
                  → a ⟿ b → a ⟿ c →
                  ∃ (λ d → b ⟿ d × c ⟿ d)
\end{code}
\end{minipage}
\begin{minipage}{0.3\textwidth}
\begin{tikzpicture}[>=latex]
   \node (a) at (2,2) {$a$};
   \node (b) at (1,1) {$b$};
   \node (c) at (3,1) {$c$};
   \node (d) at (2,0) {$d$};

   \draw [->] (a) -- (b) ;
   \draw [->] (a) -- (c) ;
   \draw[dashed,->] (b) -- (d) ;
   \draw[dashed,->] (c) -> (d) ;
\end{tikzpicture}
\end{minipage}

A relation $R$ is \emph{Church-Rosser} if its transitive closure is
diamantine; as we have already mentioned it is easier to deal with the
statement of Church-Rosser for the $n$-fold version of the transitive
closure.

\begin{code}
  cr : (⟿ : Rel) → Set l
  cr ⟿ = diamond (star ⟿)

  cr-steps : (⟿ : Rel) → Set l
  cr-steps ⟿ = diamond (steps ⟿)

  cr-steps-to-cr : {⟿ : Rel} → cr-steps ⟿ → cr ⟿
  cr-steps-to-cr cr a⟿*b a⟿*c 
    with cr (⋆-to-ω a⟿*b) (⋆-to-ω a⟿*c)
  ... | d , b⟿*d , c⟿*d = d , ω-to-⋆ b⟿*d , ω-to-⋆ c⟿*d
\end{code}

\begin{lemma}
Let $\reduction$ have the diamond property; if there is a reduction
$\reduces a b$ and also a reduction $\reducesn a c$, then there exists
$d$ such that $\reducesn b d$ and $\reduces c d$.
\end{lemma}
\begin{proof}
The proof is by induction in the length of $\reduces a c$:

\begin{tikzpicture}[>=latex,baseline]
   \node (a) at (2,2) {$a$};
   \node (b) at (1,1) {$b$};
   \node (c) at (3,1) {$a$};
   \node (d) at (2,0) {$b$};

   \draw [->] (a) -- (b) ;
   \draw [double] (a) -- (c) ;
   \draw [double] (b) -- (d) ;
   \draw[->] (c) -> (d) ;
\end{tikzpicture} 
\quad
\begin{tikzpicture}[>=latex,baseline]
   \node (a) at (2,2) {$a$};
   \node (b) at (1,1) {$b$};
   \node (c) at (3,1) {$c$};
   \node (d) at (2,0) {$d$};
   \node (diamond) at (2,1) {$\diamond$} ;

   \draw [->] (a) -- (b) ;
   \draw [->] (a) -- (c) ;
   \draw [->] (b) -- (d) ;
   \draw[->] (c) -> (d) ;
\end{tikzpicture} 
\quad
\begin{tikzpicture}[>=latex,baseline]
   \node (a) at (2,2) {$a$};
   \node (b) at (1,1) {$b$};
   \node (c1) at (3,1) {$c$};
   \node (cn) at (5,-1) {$c_n$};
   \node (d1) at (2,0) {$d_1$};
   \node (dn) at (4,-2) {$d_n$};
   \node (diamond) at (2,1) {$\diamond$} ;
   \node (ih) at (3,0) {i.h.};

   \draw [->] (a) -- (b) ;
   \draw [->] (a) -- (c1) ;
   \draw [->] (c1) -- (cn) ;
   \draw[->] (c1) -> (d1) ;
   \draw[->] (b) -> (d1) ;
   \draw[->] (d1) -> (dn) ;
   \draw[->] (cn) -> (dn) ;
\end{tikzpicture}

\end{proof}

\begin{code}
  leg :  ∀ {a b c ⟿} 
         → diamond ⟿ 
         → ⟿ a b 
         → steps ⟿ a c 
         → ∃ (λ d → steps ⟿ b d × ⟿ c d) 
  leg {a} {b} ♢ a⟿b zero    = b , zero , a⟿b 
  leg {a} {b} {c} ♢ a⟿b (one a⟿c) 
    with ♢ a⟿b a⟿c
  ... | d , b⟿d , c⟿d      = d , one b⟿d , c⟿d
  leg ♢ a⟿b (more a⟿c c⟿*dₙ) 
    with ♢ a⟿b a⟿c
  ... | d₁ , b⟿d₁ , c⟿d₁ 
    with leg ♢ c⟿d₁ c⟿*dₙ
  ... | dₙ , e⟿*dₙ , d⟿dₙ  = dₙ , more b⟿d₁ e⟿*dₙ , d⟿dₙ
\end{code}

With this result at hand is easy to prove that the diamond property
implies Church-Rosser for the $n$-fold composition of the relation.
\begin{lemma}
Let $\reduction$ be diamantine, then it satisfies Church-Rosser for the
$n$-fold closure.
\end{lemma}
\begin{proof}
The proof is by induction on the second reduction and cases in the first one, using previous result all the non trivial cases. There exists another two cases symmetrical to the first two diagrams, so we omit them.

% base case
\noindent\begin{tikzpicture}[>=latex,baseline,scale=0.8]
   \node (a) at (2,2) {$a$};
   \node (b) at (1,1) {$a$};
   \node (c) at (4,0) {$c$};
   \node (d) at (3,-1) {$c$};

   \draw [double] (a) -- (b) ;
   \draw [->] (a) -- (c) ;
   \draw[->] (b) -> (d) ;
   \draw[double] (c) -> (d) ;
\end{tikzpicture} 
% one reduction
\begin{tikzpicture}[>=latex,baseline,scale=0.8]
   \node (a) at (2,2) {$a$};
   \node (b) at (1,1) {$b$};
   \node (cn) at (4,0) {$c_n$};
   \node (dn) at (3,-1) {$d$};
   \node (ih) at (2,1) {leg};

   \draw [->] (a) -- (b) ;
   \draw [->] (a) -- (cn) ;
   \draw[->] (b) -> (dn) ;
   \draw[->] (cn) -> (dn) ;
\end{tikzpicture} 
% more steps in both sides
\begin{tikzpicture}[>=latex,baseline,scale=0.8]
   \node (a) at (2,2) {$a$};
   \node (b1) at (1,1) {$b_1$};
   \node (c1) at (3,1) {$c_1$};
   \node (bn) at (-1,-1) {$b_n$};
   \node (cn) at (5,-1) {$c_n$};
   \node (d1) at (0,-2) {$d_1$};
   \node (dn) at (2,-4) {$d_n$};
   \node (leg) at (1,0) {leg} ;
   \node (ih) at (3,-1) {i.h.};

   \draw [->] (a) -- (b1) ;
   \draw [->] (a) -- (c1) ;
   \draw [->] (b1) -- (bn) ;
   \draw [->] (c1) -- (cn) ;
   \draw[->] (c1) -> (d1) ;
   \draw[->] (bn) -> (d1) ;
   \draw[->] (d1) -> (dn) ;
   \draw[->] (cn) -> (dn) ;
\end{tikzpicture}
\end{proof}

\begin{code}
  diamond-cr-steps : {⟿ : Rel} → diamond ⟿ → cr-steps ⟿
  diamond-cr-steps ♢ {a} {.a} {c}   zero                  a⟿*c  
    = c , a⟿*c , zero
  diamond-cr-steps ♢                (one a⟿b)            a⟿*c 
    with leg ♢ a⟿b a⟿*c
  ... | d , b⟿*d , c⟿d = d , b⟿*d , one c⟿d
  diamond-cr-steps ♢ {a} {bₙ} {.a}  (more a⟿b₁ b₁⟿*bₙ)  zero 
    = bₙ , zero , more a⟿b₁ b₁⟿*bₙ
  diamond-cr-steps ♢                (more a⟿b₁ b₁⟿*bₙ)  (one a⟿c)
    with leg ♢ a⟿c (more a⟿b₁ b₁⟿*bₙ)
  ... | d , c⟿*d , bₙ⟿d = d , one bₙ⟿d , c⟿*d
  diamond-cr-steps ♢                (more a⟿b₁ b₁⟿*bₙ)  (more a⟿c₁ c₁⟿*cₙ)
    with leg ♢ a⟿c₁ (more a⟿b₁ b₁⟿*bₙ)
  ... | d₁ , c₁⟿*d₁ , bₙ⟿d₁ 
    with diamond-cr-steps ♢ c₁⟿*d₁ c₁⟿*cₙ
  ... | dₙ , d₁⟿*dₙ , cₙ⟿*dₙ  
    = dₙ , more bₙ⟿d₁  d₁⟿*dₙ , cₙ⟿*dₙ
\end{code}

Since both statements of the transitive closure are equivalent,
from cr-steps we can deduce church-rosser for any relation having
the diamond property.

\begin{code}
  diamond-cr : {⟿ : Rel} → diamond ⟿ → cr ⟿
  diamond-cr ♢ = cr-steps-to-cr (diamond-cr-steps ♢)
\end{code}

\begin{lemma} 
Let $R$ and $S$ be two relations such that $S\subseteq R$ and $\transclos R\subseteq S$, if
$R$ is Church-Rosser, then $S$ is also.
\end{lemma}
\begin{proof}
The proof is immediate: let $a\,\transclos S\,b$ and $a\,\transclos S\,c$, by the first hypothesis and $mon-star$\ lemma
we know both $a\,\transclos R\,b$ and $a\,\transclos R\,c$. By Church-Rosser for $R$ we get an element
$d$ with proofs of $b\,\transclos R\,d$ and $c\,\transclos R\,d$; by the second hypothesis and $trans-⊆-star$\ lemma we conclude
$b\,\transclos S\,d$ and $c\,\transclos S\,d$.
\end{proof}

\begin{code}
  cr-⊆ : {R S : Rel} → S ⊆ R → R ⊆ star S → cr R → cr S
  cr-⊆ S⊆R R⊆S⋆ cr aR⋆b aR⋆c
    with cr (mon-star S⊆R aR⋆b) (mon-star S⊆R aR⋆c)
  ... | d , bR⋆d , cR⋆d 
    =  d                       ,  
       trans-⊆-star R⊆S⋆ bR⋆d  , 
       trans-⊆-star R⊆S⋆ cR⋆d 
\end{code}
%</Relation>

\end{document}
