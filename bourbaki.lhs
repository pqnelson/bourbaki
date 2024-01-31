% -*- mode: LaTeX -*-
\documentclass{amsart}
%include polycode.fmt
\usepackage{amsmath,amssymb,amsthm}
\usepackage{mathrsfs}
\usepackage{graphicx}

\usepackage{xcolor}
\usepackage{hyperref}
% eTeX uses this color for links, it's better than BrickRed imho
\definecolor{linkRed}{cmyk}{0.28, 1, 1, 0.35}
\hypersetup{colorlinks=true,
    linkcolor=linkRed,
    citecolor=linkRed,
    filecolor=linkRed,
    urlcolor=linkRed
}


\def\abs#1{\lvert#1\rvert}
\DeclareMathOperator{\card}{card}
\DeclareMathOperator{\Eq}{Eq}
\def\pair{\mathrel{\rotatebox[origin=c]{180}{\textsf{C}}}}
\title{Bourbaki's Formal System in Haskell}
\author{Alex Nelson}
\date{January 7, 2024}
\urladdr{https://github.com/pqnelson/bourbaki}
\begin{document}
\maketitle

\begin{abstract}
We implement the abstract syntax tree and rudimentary syntactic support
for the formal language found in Bourbaki's \textit{Theory of Sets}~\cite{bourbaki1968sets}.
Although we do not implement any of the deductive apparatus, it should
be simple enough for a motivated reader.
\textbf{Caution:} If you are trying to run this on a computer with less
than 16 TB of RAM, then you should expect to wait a long time for it to finish.
\end{abstract}

\tableofcontents

\section{Formal Language of Bourbaki}

Bourbaki's formal system is rather difficult to understand, since it's
jettisoned almost immediately after construction, and uses many
idiosyncratic terms. My reference will be the English translation
published by Springer, the softcover reprint.\footnote{Apparently this
is the English translation dated 1968 of the French 1970 edition. How
this time-traveling is possible, well, that's beyond my understanding.}
Aitkens's commentary~\cite{aitkens2022commentary} is also worth consulting.
The basic ``Rosetta stone'' of terminology appears to be:
\begin{center}
\begin{tabular}{rcl}
Bourbaki & $\approx$ & Modern Terminology\\\hline
Sign     & $\approx$ & Letter (of a fixed ambient alphabet)\\
Assembly & $\approx$ & String (over the ambient alphabet)\\
Letter   & $\approx$ & Variable\\
Specific Sign & $\approx$ & Primitive notion (of a theory)\\
Relation & $\approx$ & Logical formula\\
Formative Criteria & $\approx$ & Formal grammar for well-formed formulas\\
\end{tabular}
\end{center}
Some terms have no modern translation, like ``logical sign'' appears to
refer to ``primitive notions in their underlying logic''.

We will hide |and| from Prelude, since it is more natural to introduce a
function which is Bourbaki's conjunction operator.
\begin{code}
import Data.Set hiding (cartesianProduct)
import Prelude hiding (and)
\end{code}

Bourbaki's ``letter'' is what we would call a ``variable''. I'm going to
encode it as an arbitrary string.

\begin{code}
type Letter = String
\end{code}

Bourbaki's ``term'' resembles what we think of terms (namely, they're
``mathematical objects'' as opposed to propositions). However, Bourbaki
uses Hilbert's $\varepsilon$-calculus, which has fallen into relative
obscurity. Complicating matters, Bourbaki uses a convoluted system of
``linkages'' to avoid distinguishing \emph{bound variables} from
\emph{free variables}.

The basic idea of Hilbert's $\varepsilon$-calculus can be understood
piecemeal. First, we think of a predicate in first-order logic as being
a term of type
\begin{spec}
type Predicate = Term -> Formula {- intuition, not actual code -}
\end{spec}
Then we can understand a ``choice operator'' as taking a predicate;
if there is an object which satisfies that predicate, then the choice
operator returns it. If there is no object which satisfies the
predicate, then an arbitrary-but-fixed object is returned. Hilbert uses
$\varepsilon_{x}P[x]$ as the notation for this term. Bourbaki sometimes uses
$\tau_{x}P[x]$ and other times replaces all instances of $x$ by a box
$\Box$, then draws ``linkages'' (i.e., lines) from those boxes to the $\tau$.
This is rather difficult to typeset. Instead, we will use de Bruijn
levels\footnote{The difference between a de Bruijn level and index
depends on where you start counting.}, and call the bound de Bruijn
level a |TBox| keeping track of the depth and the variable it replaced.

Bourbaki also introduces the notation for substituting a term $T$ for a
variable $x$ in an expression $S$ by $(T\mid x)S$. We will add this to the
abstract syntax tree encoding for a term. Later, we will create a
typeclass for syntactic classes in Bourbaki's system which support
substitutions, in order to \emph{actual perform a substiution}.

\begin{code}
data Term = TTau Integer Letter Relation
          | TBox Integer Letter
          | TVar Letter
          | TSubst Term Letter Term
          | TPair Term Term
          deriving (Show, Eq)
\end{code}

The notion of a ``formula'' in Bourbaki is called a ``relation'', which
is perhaps an unfortunate choice of words.

Bourbaki works with an adequate set of connectives, namely disjunction
$A\lor B$ and negation $\neg A$. 
The other connectives are just abbreviations for expression; in
(I~\S1.1) example 1, Bourbaki quickly mentions in as obscure a manner as
possible that:
\begin{subequations}
\begin{equation}
A\implies B \quad:=\quad (\neg A)\lor B.
\end{equation}
In (I~\S3.4), Bourbaki defines conjunction as:
\begin{equation}
A\land B\quad :=\quad \neg((\neg A)\lor(\neg B)).
\end{equation}
In (I~\S3.5), Bourbaki defines ``equivalence'' (bi-conditional) as:
\begin{equation}
A\iff B\quad :=\quad (A\implies B)\land(B\implies A).
\end{equation}
\end{subequations}
We introduce helper functions to improve the readability of encodings.

We can substitute a term for a variable in a relation, which Bourbaki
denotes by $(T\mid x)A$ where $T$ is a term and $A$ is a relation. Like
we did for terms, we are forming an abstract syntax tree for relations,
and we have a node encoding this.

The only primitives in Bourbaki's system of set theory are equality of
terms $t_{1}=t_{2}$ and set membershing $t_{1}\in t_{2}$.
\begin{code}
data Relation = ROr Relation Relation
              | RNot Relation
              | RSubst Term Letter Relation
              | REq Term Term
              | RIn Term Term
              deriving (Show, Eq)

and            :: Relation -> Relation -> Relation
and      a  b  = RNot (ROr (RNot a) (RNot b))

implies        :: Relation -> Relation -> Relation
implies  a  b  = ROr (RNot a) b

iff            :: Relation -> Relation -> Relation
iff      a  b  =  and (implies a b) (implies b a)
\end{code}


\subsection{Substitutions}

Now we can introduce a type class which abstracts the notion of
\emph{performing substitutions}. This is justified by formative criteria
CF8 from (I~\S1.4) which states that the assembly $(T\mid x)A$ is a term
when $A$ is a term, and it's a relation when $A$ is a relation.

\begin{code}
class Subst a where
  subst :: Letter -> Term -> a -> a
\end{code}

When we work with terms, we can consider the following cases:
\begin{enumerate}
\item $\displaystyle{(T\mid x)y=\begin{cases}T &\mbox{if }x=y\\y &\mbox{otherwise}\end{cases}}$
\item $(T\mid x)\tau_{x}A=\tau_{x}A$ since $x$ no longer appears in $\tau_{x}A$
\item $(T\mid x)\tau_{y}A=\tau_{y}((T\mid x)A)$ if $y\neq x$ (and we use
  the notion of substitution in a relation)
\item $(T\mid x)\Box = \Box$ since $\Box$ is ``just'' a constant term expression
\end{enumerate}
As far as $(T\mid x)\bigl((T'\mid y)T''\bigr)$ for terms $T'$, $T''$ and
variable $y$, this requires a bit of care. If $x=y$, then nothing is
done. On the other hand, if $x\neq y$, criteria CS2 (I~\S1.2) tells us
how to ``commute'' substitutions:
\begin{equation}
(B\mid x)(C\mid y)A=((B\mid x)C\mid y)(B\mid x)A.
\end{equation}
This gives us enough information to define substitution for terms:
\begin{code}
instance Subst Term where
  subst y t t' = case t' of
    (TBox _ _) -> t'
    (TVar x)  ->  if x==y
                  then t
                  else t'
    (TSubst b x a)  ->  if x==y
                        then (TSubst (subst y t b) x a)
                        else (TSubst (subst y t b) x (subst y t a))
    (TTau n x p) -> if x==y
                    then t'
                    else (TSubst t y t')
    (TPair t1 t2)  ->  TPair (subst y t t1) (subst y t t2)
\end{code}

When we work with relations, criteria of substitution CS5 from (I~\S1.2)
gives us the explicit definition for almost all relations:
\begin{enumerate}
\item $(T\mid x)(A\lor B)=((T\mid x)A)\lor((T\mid x)B)$
\item $(T\mid x)(\neg A)=\neg((T\mid x)A)$
\item $(T\mid x)(t_{1}=t_{2})\quad=\quad((T\mid x)t_{1})=((T\mid x)t_{2})$
\item $(T\mid x)(t_{1}\in t_{2})=((T\mid x)t_{1})\in((T\mid x)t_{2})$
\end{enumerate}
Bourbaki also includes in CS5 instructions for the derived connectives
$(T\mid x)(A\implies B)$, $(T\mid x)(A\land B)$, $(T\mid x)(A\iff B)$,
but these are not needed.

\begin{code}
instance Subst Relation where
  subst y t (ROr a b)  =  ROr (subst y t a) (subst y t b)
  subst y t (RNot a)   =  RNot (subst y t a)
  subst y t (RSubst b x r)  =  if y==x then (RSubst b x r)
                               else RSubst (subst y t b) x (subst y t r)
  subst y t (REq a b)  =  REq (subst y t a) (subst y t b)
  subst y t (RIn a b)  =  RIn (subst y t a) (subst y t b)
\end{code}

\subsection{Simplification}
As far as actually \emph{simplifying} expressions, we have this
operation abstracted away in its own typeclass.
\begin{code}
class Simplifier a where
  simp :: a -> a
\end{code}

There are a few sources of simplification of formulas: performing
substitutions, replacing $A\lor\neg A$ with a simpler tautology, and
eliminating double negatives.
\begin{code}
instance Simplifier Relation where
  simp (ROr a b)  =  let  a'  =  simp a
                          b'  =  simp b
                     in  if (simp (RNot a')) == b'
                         then (REq (TVar "_") (TVar "_"))
                         else if a' == b'
                         then a'
                         else ROr a' b'
  simp (RNot (RNot a))  =  simp a
  simp (RNot a)   =  RNot (simp a)
  simp (RSubst t x r)   =  simp $ subst x t r
  simp (REq a b)  =  let  a'  =  simp a
                          b'  =  simp b
                     in  if a' == b'
                         then REq (TVar "_") (TVar "_")
                         else REq (simp a) (simp b)
  simp (RIn a b)  =  RIn (simp a) (simp b)
\end{code}

Simplifying terms boils down to performing substitutions. Variables and
bound variables (|TBox|) are in simplest form.
\begin{code}
instance Simplifier Term where
  simp (TTau m x r)    =  TTau m x (simp r)
  simp (TBox m x)      =  TBox m x
  simp (TVar x)        =  TVar x
  simp (TSubst t x b)  =  simp $ subst x t b
  simp (TPair a b)     =  TPair (simp a) (simp b)
\end{code}

\subsection{*Deductive System}
Just a few remarks about the ``deductive system'' Bourbaki
uses. Specifically, Bourbaki uses a Hilbert proof calculus, but not for
first-order logic. Instead Bourbaki uses Hilbert's
$\varepsilon$-calculus. Consequently, there are only two inference rules
given (I~\S2.2):
\begin{itemize}
\item[($a_{1}$)] Any instance of an axiom may be used at any time in a proof;
\item[($a_{2}$)] Any instance of a ``scheme'' may be used at any time in a proof;
\item[($b$)] \textit{Modus Ponens}: if in previous proof steps $A$ and
  $A\implies B$ have been established, then we may write down $B$ in a
  proof step.
\end{itemize}
Axioms (I~\S2.1) are either ``explicit axioms'' (which is what we
normally think of when defining a new gadget) or ``implicit axioms'',
which are obtained by applying a scheme. Schemes are ``rules'' which
constructs a formula---Bourbaki is vague about its meaning. Derived
inference rules are given in items labeled $C1$, $C2$, $C3$, \dots.

The axioms Bourbaki gives may be found summarized in the very last page
of the book. The first four are the so-called ``Russell--Bernays
axioms''\footnote{This appears to be the axioms found in the
\textit{Principia Mathematica}, specifically corresponding to axioms
$*1.2$, $*1.3$, $*1.4$, and $*1.6$ in \textit{Principia}. Bernays proved
its logical completeness in ``Axiomatische Untersuchungen des
Aussagen-Kalkuls der \textit{Principia Mathematica}.''
\textit{Mathematische Zeitschrift} \textbf{25} (1926) 305--320;
translated into English in Richard Zach's \textit{Universal Logic: An
  Anthology} (2012) pp.43--58. Russell and Whitehead call these axioms
``principle of tautology'', ``principle of addition'',
``principle of permutation'', ``principle of
summation''. Coincidentally, this is also the axioms found in Hilbert
and Ackermann's \textit{Grundz\"{u}ge der theoretischen Logik} (1928).} (I~\S3.1) where $A\implies B$ is
understood as an abbreviation for $(\neg A)\lor B$:
\begin{itemize}
\item[(S1)] $(A\lor A)\implies A$
\item[(S2)] $A\implies(A\lor B)$
\item[(S3)] $(A\lor B)\implies(B\lor A)$
\item[(S4)] $(A\implies B)\implies((C\lor A)\implies(C\lor B))$.
\end{itemize}
Then axioms are given for quantified theories (I~\S4.2) as:
\begin{itemize}
\item[(S5)] If $R$ is a relation of theory $\mathscr{T}$, if $T$ is a
  term in $\mathscr{T}$, and if $x$ is a letter, then the relation
  $(T\mid x)R\implies(\exists x)R$ is an axiom.
\end{itemize}
The last two logical axioms concern equality (I~\S5.1):
\begin{itemize}
\item[(S6)] Let $x$ be a letter, let $T$ and $U$ be terms in theory $\mathscr{T}$,
  and let $R[x]$ be a relation in $\mathscr{T}$. Then the relation
  $(T=U)\implies(R[T]\iff R[U])$ is an axiom.
\item[(S7)] If $R$ and $S$ are relations in a theory $\mathscr{T}$,
  and if $x$ is a letter, then the relation $((\forall x)(R\iff S))\implies(\tau_{x}(R)=\tau_{x}(S))$
  is an axiom.
\end{itemize}
The usual quantifier introduction and elimination rules are given as
derived inference rules: S5 is $\exists$-introduction,
C27 is $\forall$-introduction, and
C30 is $\forall$-elimination. Existential-elimination can be given
automatically using the $\tau$-operator to obtain the witness term.

\section{Epsilon Calculus Implementation}

\subsection{De Bruijn levels}
We don't actually need to keep track of which object a $\tau_{x}A$
refers to. We encode the $\Box$ using de Bruijn levels. As a consistency
check, we keep track of the variable being bound as well as the depth of
the $\tau$ (which will match the de Bruijn level).

\begin{code}
class Shift a where
  shift :: a -> a
\end{code}

For terms, this amounts to adding 1 to the level of $\tau$ and $\Box$
instances. For substitutions, this requires shifting in both the body
and the term being substituted in.
\begin{code}
instance Shift Term where
  shift (TTau m x r)   =  TTau (m+1) x r
  shift (TBox m x)     =  TBox (m+1) x
  shift (TVar x)       =  TVar x
  shift (TSubst b x a) =  TSubst (shift b) x (shift a)
  shift (TPair a b)    =  TPair (shift a) (shift b)
\end{code}

For relations, this ``descends'' the syntax tree to terms, which are
then shifted.
\begin{code}
instance Shift Relation where
  shift (ROr a b) = ROr (shift a) (shift b)
  shift (RNot a) = RNot (shift a)
  shift (RSubst a x r) = RSubst (shift a) x (shift r)
  shift (REq a b) = REq (shift a) (shift b)
  shift (RIn a b) = RIn (shift a) (shift b)
\end{code}

\subsection{Tau operator}
The $\tau_{x}R$ can be formed using this helper function |tau x R|,
which will handle the substitution of $\Box$ for $x$ in $R$ (along with
all necessary shifting).
\begin{code}
tau      ::  Letter -> Relation -> Term
tau x r  =   TTau 0 x $ subst x (TBox 0 x) (shift r)
\end{code}

\subsection{Logical quantifiers}
We can introduce logical quantifiers (with some simplification handled
automatically) since Bourbaki follows Hilbert and defines
\begin{equation}
\exists x.A[x]\quad:=\quad A[\tau_{x}A[x]]
\end{equation}
and by de Morgan's law,\footnote{If we let $B[x]=\neg A[x]$, and using
de Morgan's law $\neg(\exists x\neg A[x])\iff\forall x.A[x]$,
then $\neg(\exists x\neg A[x])\iff\neg(\exists x.B[x])\iff\neg B[\tau_{x}B[x]]\iff \neg\neg A[\tau_{x}B[x]]$.
Double negation simplifies this to $\forall x.A[x]\iff A[\tau_{x}\neg A[x]]$.}
\begin{equation}
\forall x.A[x]\quad:=\quad A[\tau_{x}\neg A[x]].
\end{equation}
But since I'm more skeptical of accidentally writing some kind of bug,
I'm just going to use $\neg(\exists x.\neg A[x])$ as the definition for
the universal quantifier.
This gives us the code:
\begin{code}
exists         ::  Letter -> Relation -> Relation
exists  x  r   =   simp $ subst x (tau x r) r

for_all        ::  Letter -> Relation -> Relation
for_all  x  r  =   simp $ RNot (exists x (RNot r))
\end{code}
Note: the $\varepsilon$-calculus is responsible for the ridiculously
large sizes of the assemblies, specifically because we are using these
definitions of quantifiers. One bit of low-hanging fruit would be to
introduce one of these quantifiers as a primitive, and define the other
in terms of the identity $\neg(\exists x.\neg P[x])\iff\forall x.P[x]$
or $\neg(\forall x.\neg P[x])\iff\exists x.P[x]$. We would also need to
add rules to the simplifier to rewrite
\[P[\tau_{x}P[x]]\mapsto\exists x.P[x]\]
and
\[P[\tau_{x}\neg P[x]]\mapsto\forall x.P[x].\]
If we were to add axioms to support this, I suppose (since the first
four axioms describing propositional logic appear to be from Hilbert and
Ackermann, we can continue this path) we would follow
Hilbert and Ackermann's \textit{Grundz\"{u}ge der theoretischen Logik} (1928):
\begin{enumerate}
\item $(\forall x.P[x])\implies P[x]$
\item $P[x]\implies(\exists x.P[x])$.
\end{enumerate}
We would add the inference rules:
\begin{enumerate}
\item If $x$ is not free in $\varphi$ and we have proven $\varphi\implies\psi[x]$,
  then we can infer $\varphi\implies\forall x.\psi[x]$;
\item If we have proven $\psi[x]\implies\varphi$, then we can infer
  $(\exists x.\psi[x])\implies\varphi$.
\end{enumerate}

\section{Fresh Variables for Assemblies}

\subsection{Set of all variables}
We need to form the set of all variables (including, for the sake of
caution, the variables which were captured by $\tau$ expressions). 
\begin{code}
class Vars a where
  vars :: a -> Set Letter
\end{code}
For terms, this operation just descends to $\Box$ and letters, removing
any variables which are substituted out. Since we use |tau| to perform
the choice operation, substitutions should have already occurred.
\begin{code}
instance Vars Term where
  vars (TTau _ x r)    =  Data.Set.union (Data.Set.singleton x) (vars r)
  vars (TBox _ x)      =  (Data.Set.singleton x)
  vars (TVar x)        =  Data.Set.singleton x
  vars (TSubst b x a)  =  Data.Set.delete x (Data.Set.union (vars a) (vars b))
  vars (TPair a b)     =  Data.Set.union (vars a) (vars b)
\end{code}
For relations, this just descends down to terms, and form the unions of
the subtrees. As for terms, upon the substitution nodes we simply remove
the variable being replaced by terms. (And, as for terms, this shouldn't
really occur since simplification will perform the replacement.)
\begin{code}
instance Vars Relation where
  vars (ROr a b)       =  Data.Set.union (vars a) (vars b)
  vars (RNot a)        =  vars a
  vars (RSubst a x r)  =  Data.Set.delete x (Data.Set.union (vars a) (vars r))
  vars (REq a b)       =  Data.Set.union (vars a) (vars b)
  vars (RIn a b)       =  Data.Set.union (vars a) (vars b)
\end{code}

\subsection{Fresh Variables}
Given a set of variables $V$, and some variable we'd like to use $x$,
we will check if $x\in V$ and if so try some variant of $x$ to see if it
occurs in $V$. This is done by adding a subscript $x_{n}$ where $n$ is
an integer we increment upon trying again.
\begin{code}
freshVar :: Letter -> Int -> Set Letter -> Letter
freshVar x m vs  =  if (x++(show m)) `Data.Set.member` vs
                    then freshVar x (m+1) vs
                    else x++(show m)
\end{code}
Now, for any Haskell expression which is an instance of the |Vars|
typeclass, we can find a fresh variable for it. This checks if the
variable $x$ appears in the set of variables; if not, then just use
it. Otherwise, we need to find a ``fresher'' version of the variable (by
appending a numeric value ``subscript'' to it).
\begin{code}
fresh :: Vars a => Letter -> a -> Letter
fresh x fm  =  let vs = vars fm
               in  if x `elem` vs
                   then freshVar x 0 vs
                   else x
\end{code}

\section{Length of terms}

\subsection{Counting the occurrences of a variable}
How many times does a variable occur in an expression? We can count
this, using a typeclass.
\begin{code}
class Occur a where
  occur :: Letter -> a -> Integer
\end{code}
Now, $x$ doesn't appear in $\tau_{x}R$, so its occurrences should
short-circuit to zero. But if somehow it gets through, we should count
$x$ appearing zero times in $\Box$ bound variables.

For substitutions, there is some subtlety here, which is a source of
bugs in naive implementations. Observe, if $x=y$, then $(B\mid x)A$
will replace all $n$ instances of $x$ in $A$ by $B$. But if $B$ has $m$
instances of $x$, then we get $m\cdot n$ instances of $x$ in the
substitution $(B\mid x)A$.

However, when $x\neq y$, then $(B\mid y)A$ will replace all $n_{y}$
instances of $y$ in $A$ by $B$. When there are $m$ instances of $x$ in
$B$, this results in an additional $n_{y}m$ instances of $x$ in $(B\mid y)A$.
When there are $n_{x}$ instances of $x$ in $A$ \emph{before substitution},
then we have a total of $n_{y}m+n_{x}$ occurrences of $x$ in $(B\mid y)A$.
\begin{code}
instance Occur Term where
  occur x (TTau _ y r)    =  if x==y then 0 else (occur x r)
  occur x (TBox _ _)      =  0
  occur x (TVar y)        =  if x==y then 1 else 0
  occur x (TSubst b y a)  =  if x==y
                             then (occur x b)*(occur x a)
                             else (occur x b)*(occur y a)+(occur x a)
  occur x (TPair a b)     =  (occur x a) + (occur x b)
\end{code}
For relations, the same subtlety surrounding occurrences of a variable
in a substitution (but the same reasoning holds for relations as for terms).
In all other cases, it boils down to counting the occurrences in the
subtrees, and adding them all together in the end.
\begin{code}
instance Occur Relation where
  occur x (ROr a b)       =  (occur x a) + (occur x b)
  occur x (RNot a)        =  occur x a
  occur x (RSubst a y r)  =  if x==y
                             then (occur x a)*(occur x r)
                             else (occur x a)*(occur y r) + (occur x r)
  occur x (REq a b)       =  (occur x a) + (occur x b)
  occur x (RIn a b)       =  (occur x a) + (occur x b)
\end{code}

\subsection{Length of assemblies}
Now we come to the main part of the original motivation for this
program, what is the length of an assembly? For any assembly $A$, we
will write $\abs{A}$ for the length of the assembly $A$. We have a typeclass
abstracting this notion:
\begin{code}
class Len a where
  len :: a -> Integer
\end{code}
For terms, we have the inductive definition:
\begin{enumerate}
\item $\abs{\tau_{x}R}=1+\abs{R}$
\item $\abs{\Box}=1$
\item $\abs{x}=1$
\item $\abs{(B\mid x)A}=(\abs{B}-1)\cdot o(x,A)+\abs{A}$ where $o(x,A)$
  is the number of occurrences of $x$ in $A$; if one is suspicious of
  this claim, it's because $\abs{(B\mid x)A}=\abs{B}\cdot o(x,A) + (\abs{A}-o(x,A))$,
  and then simple algebra gives us the result.
\item $\abs{\langle A,B\rangle}=1+\abs{A}+\abs{B}$ since we are using
  the ``original'' convention that $\pair t_{1}\ t_{2}$ is an ordered
  pair, which just prepends the concatenation of strings with one symbol.
\end{enumerate}
\begin{code}
instance Len Term where
  len (TTau _ _ r)    =  1 + len r
  len (TBox _ _)      =  1
  len (TVar _)        =  1
  len (TSubst b x a)  =  ((len b) - 1)*(occur x a) + (len a)
  len (TPair a b)     =  1 + (len a) + (len b)
\end{code}
For relations, we have
\begin{enumerate}
\item $\abs{A\lor B}=1+\abs{A}+\abs{B}$
\item $\abs{\neg A}=1+\abs{A}$
\item $\abs{(B\mid x)R}=(\abs{B}-1)o(x,R)+\abs{R}$ where $o(x,R)$ is the
  number of occurrences of the variable $x$ in the relation $R$
\item $\abs{A=B}=1+\abs{A}+\abs{B}$
\item $\abs{A\in B}=1+\abs{A}+\abs{B}$
\end{enumerate}
\begin{code}
instance Len Relation where
  len (ROr a b)       =  1 + len a + len b
  len (RNot a)        =  1 + len a
  len (RSubst a y r)  =  ((len a) - 1)*(occur y r) + (len r)
  len (REq a b)       =  1 + len a + len b
  len (RIn a b)       =  1 + len a + len b
\end{code}

\section{Set Theory}

\textbf{Caution:} the code we implement assumes we are working with
sentences, i.e., formulas with no free variables. This is fine for our
purposes, but we should include code to make sure the variables we're
quantifying over are fresh. This adds needless overhead to our
implementation, and adds no benefit.

After C49 in (II~\S1.4), Bourbaki introduces the notation
$\mathcal{E}_{x}(R)$ for
\begin{quote}
To represent the term $\tau_{y}(\forall x)((x\in y)\iff R)$ which does
not depend on the choice of $y$ (distinct from $x$ and not appearing in
$R$), we shall introduce a functional symbol $\mathcal{E}_{x}(R)$; the
corresponding term does not contain $x$. This term is denoted by `the
set of all $x$ such that $R$'.
\end{quote}
We denote this by |ens x R|.
\begin{code}
ens  ::  Letter -> Relation -> Term
ens x r  =  let y = fresh "y" r
            in tau y (for_all x (iff (RIn (TVar x) (TVar y)) r))
\end{code}
The unordered pair is introduced in (II~\S1.5), defined as
$\mathcal{E}_{z}(x=z\lor y=z)$ which is then abbreviated as $\{x,y\}$.
This exists and is unique by the second axiom of Bourbaki's set theory,
which means it really is a well-defined notion.
\begin{code}

-- The set with two elements, a.k.a., the unordered pair.
pair      ::  Term -> Term -> Term
pair x y  =   let z = fresh "z" (REq x y)
              in ens z (ROr (REq x (TVar z)) (REq y (TVar z)))
\end{code}

\subsection{Ordered Pairs} This is formalized in (II~\S2) of Bourbaki's
\textit{Theory of Sets}. Bourbaki defines $\pair T\ U$ for the
ordered pair of $T$ and $U$ as a primitive notion. But we can use the
usual set-theoretic construction of ordered pairs. Purists can modify
code in the way following explicit instructions.

Now, before we can define the ordered pair using the familiar
set-theoretic definition $(x,y)=\{\{x\},\{x,y\}\}$, we need to define an
unordered singleton.
\begin{code}
ssingleton    ::  Term -> Term
ssingleton x  =   let z = fresh "z" x
                  in ens z (REq x (TVar z))
\end{code}
Now, for ordered pairs, we use the set-theoretic definition for
debugging purposes (if you wanted to use the original Bourbaki
formulation, you can replace this line of code with the primitive
|TPair| data constructor)
\begin{code}
--- use orderedPair = TPair for debugging purposes
orderedPair    ::  Term -> Term -> Term
orderedPair    =   TPair
-- orderedPair    x  y     =  pair (ssingleton x) (pair x y)

orderedTriple  ::  Term -> Term -> Term -> Term
orderedTriple  x  y  z  =  orderedPair (orderedPair x y) z
\end{code}

\subsection{Cartesian Product of Sets}
The Cartesian product of sets is defined in (II~\S2.2) Definition~1 as
\begin{equation}
X\times Y := \mathcal{E}_{z}\bigl((\exists x)(\exists y)(z=(x,y)\land x\in X\land y\in Y)\bigr).
\end{equation}
The implementation follows this definition:
\begin{code}
cartesianProduct :: Term -> Term -> Term
cartesianProduct x y = ens "z"  (exists "x'"
                                  (exists "y'"
                                    (and  (REq  (TVar "z") 
                                                (orderedPair (TVar "x'") (TVar "y'")))
                                          (and  (RIn (TVar "x'") x)
                                                (RIn (TVar "y'") y)))))
\end{code}

\subsection{Subsets}
In (II~\S1.2), Definition~1, Bourbaki defines the predicate for a subset
$X\subset Y$ as:
\begin{equation}
X\subset Y\quad :=\quad \forall z(z\in X\implies z\in Y).
\end{equation}
We use this definition in the construction:
\begin{code}
subset :: Term -> Term -> Relation
subset u v = for_all "s" (implies (RIn (TVar "s") u) (RIn (TVar "s") v))
\end{code}

\subsection{Empty set}
The empty set is defined as $\tau_{X}((\forall y)(y\notin X))$ in
comments towards the end of (II~\S1.7), and we use this as the definition
for it:
\begin{code}
emptySet :: Term
emptySet = tau "X" (for_all "y" (RNot (RIn (TVar "y") (TVar "X"))))
\end{code}

\subsection{Cardinality of sets}
In (III~\S3.1), Bourbaki defines the notion of ``the cardinal of a set''
using equipotential sets.
Two sets $A$ and $B$ are called equipotent, denoted by Bourbaki as
$\Eq(A,B)$, if there exists a bijection between sets $A$ and $B$.
Then the cardinality of a set $A$ is defined as $\card(A):=\tau_{Z}(\Eq(A,Z))$.
But in a footnote, Bourbaki tells us the explicit definition for 
$1:=\card(\{\emptyset\})$. It's tedious:
\begin{multline}
  \tau_{Z}\biggl(
(\exists u)(\exists U)\Bigl(u=(U,\{\emptyset\},Z)\mbox{ and }U\subset\{\emptyset\}\times Z\\
\mbox{and }(\forall x)\bigl((x\in\{\emptyset\})\implies(\exists y)((x,y)\in U)\bigr)\\
\mbox{and }(\forall x)(\forall y)(\forall y')\bigl(((x,y)\in U\mbox{ and }(x,y')\in U)\implies(y=y')\bigr)\\
\mbox{and }(\forall y)((y\in Z)\implies(\exists x)((x,y)\in U))\Bigr)
\biggr)
\end{multline}
This allows us to find the primitive definition of $\card(A)$:
\begin{multline}
\card(A):=\tau_{Z}\biggl(
(\exists u)(\exists U)\Bigl(u=(U,A,Z)\mbox{ and }U\subset A\times Z\\
\mbox{and }(\forall x)\bigl((x\in A)\implies(\exists y)((x,y)\in U)\bigr)\\
\mbox{and }(\forall x)(\forall y)(\forall y')\bigl(((x,y)\in U\mbox{ and }(x,y')\in U)\implies(y=y')\bigr)\\
\mbox{and }(\forall y)((y\in Z)\implies(\exists x)((x,y)\in U))\Bigr)
\biggr)
\end{multline}
Here is where all the low-hanging fruit for optimization occurs, we
could use different definitions of cardinality. There are five terms in
this definition contained in the scope of the outer two universal
quantifiers $\forall u\forall U(\dots)$ which we define as |termA|,
|termB|, |termC|, |termD|, and |termE|. We faithfully write the
code for this convoluted definition:
\begin{code}
termA :: Term -> Letter -> Letter -> Letter -> Relation
termA x u upperU z = REq (TVar u) (orderedTriple (TVar upperU) x (TVar z))

termB :: Term -> Letter -> Letter -> Relation
termB x upperU z = subset (TVar upperU) (cartesianProduct x (TVar z))

termC :: Term -> Letter -> Relation
termC x upperU = for_all "x" (implies  (RIn (TVar "x") x)
                                       (exists "y" (RIn  (orderedPair (TVar "x") (TVar "y"))
                                                         (TVar upperU))))

termD :: Letter -> Relation
termD upperU = for_all "x"
  (for_all "y" (for_all "z"
                 (implies  (and  (RIn (orderedPair (TVar "x") (TVar "y")) (TVar upperU))
                                 (RIn (orderedPair (TVar "x") (TVar "z")) (TVar upperU)))
                           (REq (TVar "y") (TVar "z")))))

termE :: Letter -> Letter -> Relation
termE upperU z = for_all "y" (implies
                               (RIn (TVar "y") (TVar z))
                               (exists "x" (RIn  (orderedPair (TVar "x") (TVar "y"))
                                                 (TVar upperU))))

card :: Term -> Term
card x = tau "Z" (exists "u" (exists "U" (and  (termA x "u" "U" "Z")
                                               (and  (termB x "U" "Z")
                                                     (and  (termC x "U")
                                                           (and  (termD "U")
                                                                 (termE "U" "Z")))))))
\end{code}
As examples of this definition, Bourbaki defines 1 and 2 as
\begin{code}
one :: Term
one = card (ssingleton emptySet)

two :: Term
two = card (pair emptySet (ssingleton emptySet))
\end{code}

\subsection{Sums}
The value $f(x)$ corresponding to $x$ of a function $f$, when $G$ is the
graph of $f$, is (slightly optimized) the $y$ such that $(x,y)$ is in $G$.
Bourbaki defines (II~\S3.1, definition 3, remark 1) the image of a
set X according to a graph $G$ as
\begin{spec}
ens y (exists "x" (and  (RIn (TVar "x") X)
                        (RIn (orderedPair (TVar "x") y) G)))
\end{spec}
But since $X$ is a singleton for our case, we don't need to check $x\in\{x\}$.
I further simplify things and just say the value of $x$ in $G$ is that
$y$ such that $(x,y)\in G$.
\begin{code}
val :: Term -> Term -> Term
val x graph = tau "y" (RIn (orderedPair x (TVar "y")) graph)
\end{code}

In a remark after Proposition 5 (III~\S3.3), Bourbaki notes
if $a$ and $b$ are two cardinals, and $I$ a set with two elements (e.g.,
the cardinal 2), then there exists a mapping $f$ of $I$ onto $\{a, b\}$
for which the sum of this family is denoted $a+b$.

The sum of a family of sets is discussed in (II~\S4.8) Definition~8 gives it as:
\begin{quote}
Let $(X_{i})_{i\in I}$ be a family of sets.
The sum of this family is the union of the family of sets $(X_{i}\times \{i\})_{i\in I}$.
\end{quote}
The notion of a family of sets is defined in (II~\S3.4). It is basically the graph of a function $I\to \{X_{i}\}$.

The union of a family of sets $(X_{i})_{i\in I}$ is (II~\S4.1 Definition~1)
$\mathcal{E}_{x}(\exists i)((i\in I)\mbox{ and }(x\in X))$
% ens x (exists "i" (and (RIn (TVar "i") I) (RIn (TVar x) X)))
The family $\{X_{0}, X_{1}\}$ when $X_{0}=X_{1}=1$ is then |cartesianProduct two one|.
Combining this together, we get the sum as:
\begin{code}
setSum :: Term -> Term -> Term
setSum idx family = ens "x"  (exists "i"
                               (and  (RIn (TVar "i") idx)
                                     (RIn (TVar "x") (val (TVar "i") family))))
\end{code}

When $a$ and $b$ are cardinal numbers, Bourbaki uses the indexed family
$\{f_{1}, f_{2}\}$ where $f_{1}=a$ and $f_{2}=b$.  This indexed family
coincides with the cartesian product of the cardinality 2 with the
unordered pair $\{a, b\}$. Then the sum of this family is the sum of
cardinals.
\begin{code}
cardSum :: Term -> Term -> Term
cardSum a b = setSum two (cartesianProduct two (pair a b))
\end{code}
Now, the big moment, the equation asserting $1+1=2$.
\begin{code}
onePlusOneIsTwo :: Relation
onePlusOneIsTwo = REq two (cardSum one one)
\end{code}

\subsection{Curiousities}
I was curious about the length of various terms, so I defined them.
\begin{code}
pairOfOnes :: Term
pairOfOnes = pair one one

productTwoOnes :: Term
productTwoOnes = cartesianProduct two pairOfOnes
\end{code}

\section{Main Method}
OK, ready? Your pulse is relaxed, you don't need a wet towel on your
forehead or anything? Good, now we have the main method which will print
out the statistics regarding the lengths of the various things:
\begin{code}

main = do
  putStrLn ("The size of {x, y} = " ++ (show (len (pair (TVar "x") (TVar "y")))))
  putStrLn ("Size of (x, y) = " ++ (show (len (orderedPair (TVar "x") (TVar "y")))))
  putStrLn ("Size of the Empty Set = " ++ (show (len emptySet)))
  putStrLn ("Size of $X\\times Y$ = " ++ (show (len (cartesianProduct (TVar "X") (TVar "Y")))))
  putStrLn ("Size of       1   = " ++ (show (len one)))
  putStrLn ("Size of `{1,1}`   = " ++ (show (len pairOfOnes)))
  putStrLn ("Size of `2*{1,1}` = " ++ (show (len productTwoOnes)))
  putStrLn ("Size of '1+1=2' = " ++ (show (len onePlusOneIsTwo)))
  putStrLn ("Size of 1*      = " ++ (show (len (simp one))))
  putStrLn ("Size of A = " ++ (show (len (termA (ssingleton emptySet) "u" "U" "Z"))))
  putStrLn ("Size of B = " ++ (show (len (termB (ssingleton emptySet) "U" "Z"))))
  putStrLn ("Size of C = " ++ (show (len (termC (ssingleton emptySet) "U"))))
  putStrLn ("Size of D = " ++ (show (len (termD "U"))))
  putStrLn ("Size of E = " ++ (show (len (termE "U" "Z"))))
\end{code}


\begin{thebibliography}{99}
\bibitem{bourbaki1968sets} Nicolas Bourbaki, \textit{The Theory of Sets}.
  Springer, 2000 softcover reprint of 1968 English translation.
\bibitem{aitkens2022commentary} Wayne Aitken,
  ``Bourbaki, Theory of Sets, Chapter I, Description of Formal Mathematics: Summary and Commentary''.
  Commentary dated 2022, \url{https://public.csusm.edu/aitken_html/Essays/Bourbaki/BourbakiSetTheory1.pdf}
\end{thebibliography}
\end{document}
