# Joint hypertranscendence of Hurwitz zeta functions in the shift parameter

## Abstract

Fix a finite family $s_1,\ldots,s_r\in\mathbb C$ with $\operatorname{Re}s_j>1$, and set
$q_j=e^{-2\pi i s_j}$. Suppose that distinct nonnegative monomials in
$(q_1,\ldots,q_r)$ have distinct values. We prove that, for every $N\geq 0$, the functions

\[
  \zeta(s_j+k,a),\qquad 1\leq j\leq r,\quad 0\leq k\leq N,
\]

are algebraically independent over $\mathbb C(a)$. Consequently the functions
$a\mapsto\zeta(s_1,a),\ldots,a\mapsto\zeta(s_r,a)$ satisfy no nonzero mixed algebraic
differential equation over $\mathbb C(a)$. A sufficient arithmetic condition is the rational
linear independence of $1,s_1,\ldots,s_r$. The proof combines simultaneous branch monodromy,
Zariski density of a common cyclic power orbit, independent branch-point columns, and a
block-Vandermonde automorphism.

## 1. Introduction

For $\operatorname{Re}s>1$ and $\operatorname{Im}a>0$, write

\[
  \zeta(s,a)=\sum_{n=0}^{\infty}(n+a)^{-s},                 \tag{1.1}
\]

using the principal logarithm. Differentiation in the shift variable raises the exponent:

\[
  \partial_a^k\zeta(s,a)=(-1)^k(s)_k\zeta(s+k,a),          \tag{1.2}
\]

where $(s)_k=s(s+1)\cdots(s+k-1)$. Thus algebraic independence of complete finite shift
ladders is equivalent to algebraic independence of complete finite differential jets.

The decisive feature is simultaneous monodromy. A loop around the branch point $-n$ multiplies
the $n$-th summand in every exponent family by its corresponding scalar

\[
  q_j=e^{-2\pi i s_j}.                                      \tag{1.3}
\]

One loop count is shared by all $j$; the exponent coordinates cannot be varied independently.
The correct arithmetic datum is therefore the common power orbit
$m\mapsto(q_1^m,\ldots,q_r^m)$. When its monomials are separated, this orbit is Zariski dense.
Loops about different branch points then supply independent copies of that orbit. A
block-Vandermonde map turns the resulting product grid into arbitrary ladder values.

This produces a joint statement. Individual hypertranscendence theorems do not rule out a mixed
differential equation coupling several Hurwitz zeta functions; the theorem below does.

## 2. The monodromy-character law

Let $I$ be a nonempty finite index set, let $s=(s_j)_{j\in I}$, and put
$q_j=e^{-2\pi i s_j}$. For a finitely supported exponent vector
$\alpha\in\mathbb N^{I}$, write

\[
  q^\alpha=\prod_{j\in I}q_j^{\alpha_j}.
\]

We use the intrinsic nonresonance condition

\[
  \alpha\longmapsto q^\alpha
  \quad\text{is injective on }\mathbb N^{I}.                \tag{NR}
\]

For $N\geq0$, define the finite ladder

\[
  \mathcal L_N(s)=
  \bigl(\zeta(s_j+k,a)\bigr)_{j\in I,\ 0\leq k\leq N}.
\]

### Theorem 2.1 — monodromy-character law

Assume $\operatorname{Re}s_j>1$ for every $j\in I$ and condition **(NR)**. Then, for every
$N\geq0$, the entries of $\mathcal L_N(s)$ are algebraically independent over
$\mathbb C(a)$.

More explicitly, the polynomial-coefficient form says that if

\[
  P\in\mathbb C[a][Y_{j,k}:j\in I,\ 0\leq k\leq N]
\]

and

\[
  P\bigl(a;(\zeta(s_j+k,a))_{j,k}\bigr)=0
  \qquad(\operatorname{Im}a>0),                             \tag{2.1}
\]

then $P=0$. For $Q\in\mathbb C(a)[Y_{j,k}]$, let $\widetilde Q\in\mathbb C[a][Y_{j,k}]$
be obtained by multiplying all coefficients by the product of their reduced denominators. If the
identity (2.1) holds with $\widetilde Q$ in place of $P$, then $Q=0$.

### Corollary 2.2 — arithmetic joint ladder independence

Let $s_1,\ldots,s_r\in\mathbb C$ satisfy $\operatorname{Re}s_j>1$. If
$1,s_1,\ldots,s_r$ are linearly independent over $\mathbb Q$, then for every $N\geq0$ the
$r(N+1)$ functions

\[
  \zeta(s_j+k,a),\qquad 1\leq j\leq r,\quad0\leq k\leq N,
\]

are algebraically independent over $\mathbb C(a)$.

### Corollary 2.3 — joint differential algebraic independence

Under either the intrinsic hypotheses of Theorem 2.1 or the arithmetic hypotheses of
Corollary 2.2, for every $N\geq0$ the functions

\[
  \partial_a^k\zeta(s_j,a),
  \qquad j\in I,\quad0\leq k\leq N,                         \tag{2.2}
\]

are algebraically independent over $\mathbb C(a)$. Hence no nonzero mixed algebraic
differential equation of finite order and degree over $\mathbb C(a)$ couples the family
$a\mapsto\zeta(s_j,a)$.

## 3. Power-orbit density

The first algebraic lemma isolates the common-time constraint.

### Lemma 3.1 — cyclic power-orbit density

Let $q=(q_j)_{j\in I}\in(\mathbb C^\times)^I$ satisfy **(NR)**. If
$R\in\mathbb C[X_j:j\in I]$ and

\[
  R((q_j^m)_{j\in I})=0\qquad\text{for every }m\in\mathbb N, \tag{3.1}
\]

then $R=0$.

#### Proof

Write $R=\sum_{\alpha\in A}c_\alpha X^\alpha$, with $A$ finite. Equation (3.1) gives

\[
  \sum_{\alpha\in A}c_\alpha(q^\alpha)^m=0
  \qquad(m\in\mathbb N).                                   \tag{3.2}
\]

The bases $q^\alpha$ are pairwise distinct by **(NR)**. Evaluating (3.2) for
$m=0,\ldots,|A|-1$ gives an invertible Vandermonde system, so every $c_\alpha$ is zero. ∎

### Lemma 3.2 — product power-grid density

Let $L\geq1$. If a polynomial in the variables
$(X_{j,n})_{j\in I,\ 0\leq n<L}$ vanishes at every point

\[
  X_{j,n}=q_j^{m_n},
  \qquad(m_0,\ldots,m_{L-1})\in\mathbb N^L,                 \tag{3.3}
\]

then it is the zero polynomial.

#### Proof

Fix all columns except one and apply Lemma 3.1 to the remaining column. It may then be replaced by
an arbitrary point of $\mathbb C^I$. Repeating this argument one column at a time proves the
claim. ∎

### Lemma 3.3 — rational independence implies **(NR)**

If $1$ together with $(s_j)_{j\in I}$ is linearly independent over $\mathbb Q$, then the scalars
$q_j=e^{-2\pi i s_j}$ satisfy **(NR)**.

#### Proof

If $q^\alpha=q^\beta$, then

\[
  \exp\!\left(-2\pi i\sum_{j\in I}(\alpha_j-\beta_j)s_j\right)=1.
\]

Hence $\sum_j(\alpha_j-\beta_j)s_j\in\mathbb Z$. Rational linear independence of
$1$ and the $s_j$ forces $\alpha=\beta$. ∎

## 4. Simultaneous branch deformation

Fix $N\geq0$ and introduce parameters
$c=(c_{j,n})_{j\in I,\ 0\leq n\leq N}$. For $0\leq k\leq N$, set

\[
  F_{j,k}^{c}(a)=\zeta(s_j+k,a)
    +\sum_{n=0}^{N}(c_{j,n}-1)(a+n)^{-s_j-k}.                \tag{4.1}
\]

The original ladder is $F^{\mathbf 1}$.

### Proposition 4.1 — simultaneous monodromy update

Let

\[
  P\in\mathbb C[a][Y_{j,k}:j\in I,\ 0\leq k\leq N]
\]

and suppose that

\[
  P(a;F^c(a))=0\qquad(\operatorname{Im}a>0).                \tag{4.2}
\]

For any $n\in\{0,\ldots,N\}$, the same identity holds after the simultaneous update

\[
  c_{j,n}\longmapsto q_jc_{j,n}\qquad(j\in I),              \tag{4.3}
\]

with every other column fixed.

#### Proof

Put $a=-n+e^z$. On $0<\operatorname{Im}z<\pi$, separation of the $n$-th summand gives

\[
  F_{j,k}^{c}(-n+e^z)
  =c_{j,n}e^{-(s_j+k)z}+T_{j,k,n}^{c}(e^z),                 \tag{4.4}
\]

where the tail is holomorphic for $|e^z|<1/2$. Substitution into $P$ produces a holomorphic
function on the connected half-plane $\operatorname{Re}z<-\log2$. It vanishes on the upper
strip slice and therefore on the whole half-plane. Translation by $2\pi i$ leaves $e^z$, the
coefficient polynomials, and all tail terms unchanged, while

\[
  e^{-(s_j+k)(z+2\pi i)}=q_j e^{-(s_j+k)z}.                 \tag{4.5}
\]

Translating the identity and returning to the $a$-plane gives (4.3) throughout the upper
half-plane. ∎

Iterating Proposition 4.1 independently at the branch points $0,-1,\ldots,-N$ gives

\[
  P(a;F^{c(m)}(a))=0,
  \qquad c(m)_{j,n}=q_j^{m_n},quad m\in\mathbb N^{N+1}.     \tag{4.6}
\]

This is the product grid of Lemma 3.2. Notice that each branch point supplies an independent
column, while every column retains the common-time coupling across $j$.

## 5. Proof of the monodromy-character law

First take $P$ with coefficients in $\mathbb C[a]$ and suppose (2.1) vanishes throughout the
upper half-plane. Fix $a$ there. Equations (4.6) and Lemma 3.2 imply that

\[
  c\longmapsto P(a;F^c(a))                                  \tag{5.1}
\]

is the zero polynomial on $\mathbb C^{I\times\{0,\ldots,N\}}$.

For each $j$, the linear part of $c_{j,\bullet}\mapsto
(F_{j,k}^c(a))_{0\leq k\leq N}$ is

\[
  W^{(j)}_{k,n}(a)
  =(a+n)^{-s_j-k}
  =(a+n)^{-s_j}\bigl((a+n)^{-1}\bigr)^k.                   \tag{5.2}
\]

Its determinant is

\[
  \det W^{(j)}(a)=
  \left(\prod_{n=0}^{N}(a+n)^{-s_j}\right)
  \prod_{0\leq n<m\leq N}
  \left((a+m)^{-1}-(a+n)^{-1}\right),                      \tag{5.3}
\]

which is nonzero. The full deformation map is block diagonal with these invertible blocks, hence
is an affine automorphism. Therefore (5.1) implies

\[
  P(a;y)=0\qquad\text{for every }y\in\mathbb C^{I\times\{0,\ldots,N\}}. \tag{5.4}
\]

Every coefficient of $P$, viewed as a polynomial in $a$, vanishes at every point of the upper
half-plane, so $P=0$.

For coefficients in $\mathbb C(a)$, multiply a proposed relation by the product of the reduced
denominators of its finitely many nonzero coefficients. The resulting polynomial-coefficient
relation is zero, and this clearing operation preserves nonzeroness. Thus the original relation is
zero. This proves Theorem 2.1. Lemma 3.3 gives Corollary 2.2.

Finally, (1.2) is an invertible diagonal change of coordinates on every finite jet because
$\operatorname{Re}s_j>1$ makes each $(s_j)_k$ nonzero. Applying Theorem 2.1 after this change of
coordinates proves Corollary 2.3. ∎

## 6. Scope and relation to previous work

The multivalued analytic continuation and linear monodromy spaces of the Hurwitz–Lerch family are
developed by Lagarias and Li. Costin and Garoufalidis analyze related monodromy for fractional
polylogarithms. Those results concern the analytic continuation and the linear space of branches;
the theorem here concerns nonlinear algebraic relations among fixed-exponent functions of the shift
variable.

Differential-transcendence results of Amou and Katsurada treat generalized Dirichlet series in the
Dirichlet-series variable, with the shift fixed. Functional-independence results for periodic
Hurwitz zeta functions likewise concern the Dirichlet-series variable. The present theorem fixes
the exponents and differentiates in the shift variable. Its joint content is the exclusion of
mixed equations across a finite exponent family.

The theorem is sufficient, not a converse: failure of **(NR)** reduces the Zariski closure of the
common monodromy orbit and therefore reduces the deformation space supplied by this proof. No
dependence assertion is made in that case.

## References

1. M. Amou and M. Katsurada, “Differential transcendence of a class of generalized Dirichlet
   series,” *Illinois Journal of Mathematics* **45** (2001), 939–948.
   [doi:10.1215/ijm/1258138161](https://doi.org/10.1215/ijm/1258138161).
2. O. Costin and S. Garoufalidis, “Resurgence of the fractional polylogarithms,”
   *Mathematical Research Letters* **16** (2009), 817–826.
   [doi:10.4310/MRL.2009.v16.n5.a5](https://doi.org/10.4310/MRL.2009.v16.n5.a5).
3. NIST Digital Library of Mathematical Functions, §25.11, “Hurwitz Zeta Function,” especially
   Eq. 25.11.17. [https://dlmf.nist.gov/25.11](https://dlmf.nist.gov/25.11).
4. J. C. Lagarias and W.-C. W. Li, “The Lerch zeta function II. Analytic continuation,”
   *Forum Mathematicum* **24** (2012), 49–84.
   [doi:10.1515/FORM.2011.048](https://doi.org/10.1515/FORM.2011.048).
5. J. C. Lagarias and W.-C. W. Li, “The Lerch zeta function III. Polylogarithms and special
   values,” *Research in the Mathematical Sciences* **3** (2016), Article 2.
   [arXiv:1506.06161](https://arxiv.org/abs/1506.06161).
6. A. Laurinčikas, “Functional independence of periodic Hurwitz zeta functions,”
   *Mathematical Notes* **83** (2008), 65–71.
   [doi:10.1134/S0001434608010082](https://doi.org/10.1134/S0001434608010082).
7. A. Ostrowski, “Über Dirichletsche Reihen und algebraische Differentialgleichungen,”
   *Mathematische Zeitschrift* **8** (1920), 241–298; English translation by E. C. Hansen,
   Y. Stone, and J. Wolfson, [arXiv:2211.02088](https://arxiv.org/abs/2211.02088).
