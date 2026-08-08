# Route E product-truncated reservoir harmonic-mass law

- **ID:** `ROUTE-E-PRODUCT-TRUNCATED-RESERVOIR-MASS-001`
- **Stage:** 2-fully-proven
- **Type:** `[PAPER-PROVED] [EXACT FINITE INEQUALITY] [WHOLE-ANCHOR FRONTIER REDUCTION]`
- **Parent:** `route-e-whole-anchor-capacity-displacement-conservation-law.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** not started; Lean corpus was read only during active refactor
- **Scientific status:** project-local new synthesis; external priority unclaimed

## 1. Exact theorem

Let \({\mathcal P}\) be a nonempty finite prime set and put

\[
 S=\sum_{p\in{\mathcal P}}\frac1p,
 \qquad
 Q=\sum_{p\in{\mathcal P}}\frac1{p^2},
 \qquad
 A=\sum_{p\in{\mathcal P}}\frac{\log p}{p}.
\tag{1}
\]

For \(b\ge1\) and \(T>1\), define exact-breadth product-truncated harmonic mass

\[
 H_b(T;{\mathcal P})
 =\sum_{\substack{R\subseteq{\mathcal P}\\|R|=b\\\prod_{p\in R}p\le T}}
   \prod_{p\in R}\frac1p.
\tag{2}
\]

Set

\[
 \eta_b=\binom b2\frac Q{S^2}.
\tag{3}
\]

Then unconditional finite inequality is

\[
 \boxed{
 H_b(T;{\mathcal P})
 \ge \frac{S^b}{b!}
 \left(1-\eta_b-\frac{bA}{S\log T}\right).}
\tag{4}
\]

In particular, if \(\eta_b=o(1)\), \(b/S\le R\), and

\[
 A\le(c+o(1))\log T
\quad\text{for one }c<1/R,
\tag{5}
\]

then

\[
 \boxed{
 H_b(T;{\mathcal P})
 \ge(1-cR-o(1))\frac{S^b}{b!}.}
\tag{6}
\]

Thus product truncation at \(T\) retains a positive proportion of full elementary-symmetric
harmonic mass.  Requiring every individual prime to be at most \(T^{1/b}\) is unnecessary and
can lose a full logarithmic factor.

## 2. Collision lower bound for elementary-symmetric mass

Expanding \(S^b\) counts ordered \(b\)-tuples of primes, with repetition.  Ordered tuples with
all entries distinct contribute exactly

\[
 b!\,e_b((1/p)_{p\in{\mathcal P}}).
\tag{7}
\]

For a fixed pair of positions, repeated-coordinate contribution is \(QS^{b-2}\).  Union bound
over \(\binom b2\) pairs gives

\[
 S^b-b!e_b((1/p)_{p\in{\mathcal P}})
 \le\binom b2QS^{b-2}.
\tag{8}
\]

Therefore

\[
 \boxed{
 e_b((1/p)_{p\in{\mathcal P}})
 \ge(1-\eta_b)\frac{S^b}{b!}.}
\tag{9}
\]

This estimate is effective whenever prime weights have negligible second moment at breadth \(b\).

## 3. Product tail costs only its logarithmic first moment

Let

\[
 M_b=\sum_{\substack{R\subseteq{\mathcal P}\\|R|=b}}
 \left(\prod_{p\in R}\frac1p\right)
 \log\left(\prod_{p\in R}p\right).
\tag{10}
\]

Mark one prime in each subset.  Then

\[
 M_b
 =\sum_{p\in{\mathcal P}}\frac{\log p}{p}
   e_{b-1}((1/q)_{q\in{\mathcal P}\setminus\{p\}})
 \le A\frac{S^{b-1}}{(b-1)!},
\tag{11}
\]

because \((b-1)!e_{b-1}\le S^{b-1}\).  Every subset with product greater than \(T\) contributes
at least \(\log T\) times its harmonic weight to `(10)`.  Hence

\[
 \sum_{\substack{|R|=b\\\prod R>T}}\frac1{\prod R}
 \le\frac{A}{\log T}\frac{S^{b-1}}{(b-1)!}
 =\frac{S^b}{b!}\frac{bA}{S\log T}.
\tag{12}
\]

Subtract `(12)` from `(9)` to prove `(4)`.

## 4. Cofinal Route E specialization

Put

\[
 L=\log\log X,qquad
 W=(\log X)^{A_0}\quad(A_0>2),qquad
 T=X^{1/g(L)},
\tag{13}
\]

where

\[
 g(L)\longrightarrow\infty,qquad
 \log g(L)=o(\sqrt L).
\tag{14}
\]

Choose one fixed \(c\in(0,1/4)\) and

\[
 {\mathcal P}_X=\{p:W<p\le T^c\}.
\tag{15}
\]

Mertens prime-sum asymptotics and PNT partial summation give

\[
 \begin{aligned}
 S_X&=L-\log L-\log g(L)+O(1),\\
 A_X&=(c+o(1))\log T,\\
 Q_X&\le\sum_{n>W}n^{-2}=O(W^{-1}).
 \end{aligned}
\tag{16}
\]

Uniformly for \(L/2\le b\le2L\), one has \(b/S_X\le3\) for large \(X\), and
\(\eta_b=o(1)\).  Taking, for example, \(c=1/10\), `(6)` yields

\[
 \boxed{
 H_b(T;{\mathcal P}_X)
 \ge\left(\frac7{10}-o(1)\right)\frac{S_X^b}{b!}}
\tag{17}
\]

for every central breadth \(b\).  Every retained reservoir product obeys

\[
 t_R\le T=X^{1/g(L)}=X^{o(1)},
\tag{18}
\]

so square-root displacement remains \(X^{1/2+o(1)}\).  Lower edge \(W>(\log X)^2\) still
separates reservoir primes from small structured token factor; upper selected primes are
\(X^{o(1)}\), far below balanced large token factors.

At normal breadth \(b=L+O(\sqrt L)\), Stirling and `(16)` give representative scale

\[
 \boxed{
 H_b(T;{\mathcal P}_X)
 \ge \frac{\log X}{g(L)L^{3/2}}
       \exp\!\left(-O\left(\frac{(b-L)^2+(\log L+\log g)^2}{L}\right)
             -O(1)\right).}
\tag{19}
\]

This is exponentially larger in \(\sqrt L\) than proposed full-allocation band of parent card,
while preserving critical displacement.

## 5. What theorem closes and what it does not

Parent conservation law left one possible escape: use high-band reservoir primes but predeclare
only subsets whose product is \(X^{o(1)}\).  Equation `(17)` proves harmonic-row half of that
escape.  Product truncation is not automatically harmonically sparse.

It does not prove unit physical column load.  For fixed terminal, reservoir is decoded from band
support, but incoming source count still requires sharp local \(\omega=s\) layer law and token
supply on inverse square-root interval.  Exact mass `(17)` cannot replace those two incidence
inputs.

In particular, if token theorem supplies \(N_R\) choices in a physical interval of length
\(h_R\), schematic column factor is

\[
 \frac{h_R}{t_RN_R}\,
 \frac{\text{local source-layer density}}{H_b(T;{\mathcal P}_X)}.
\tag{20}
\]

Equation `(17)` closes denominator.  It gives no upper bound for first factor or local layer
density.

## 6. Conjecture--proof--failure loops

### Loop A: product truncation destroys harmonic mass

`[CONJECTURE]` Restricting \(t_R\le X^{o(1)}\) necessarily leaves only \(o(1)\) proportion of
exact-breadth reciprocal mass.

`[FALSIFIED]` Finite inequality `(4)` and Route E specialization `(17)` retain a fixed positive
proportion.

### Loop B: cap every prime at \(T^{1/b}\)

`[CONJECTURE]` Deterministic coordinatewise cap is needed to ensure product bound.

`[FALSIFIED AS WASTEFUL]` Coordinatewise cap decreases reciprocal mass by approximately
\(\log b\).  Weighted Markov estimate `(12)` enforces same product condition after subset
formation and loses only fixed constant.

### Loop C: recovered row mass proves unit Carleson

`[CONJECTURE]` Equation `(17)` completes whole-anchor route.

`[FAILED]` Column expression `(20)` still contains local source layer and short-interval token
density.  Neither is bounded by elementary-symmetric mass.

### Loop D: representation multiplicity supplies missing columns

`[CONJECTURE]` Product-truncated labels can be counted as independent capacity.

`[FALSIFIED BY PARENT CONSERVATION LAW]` Capacity is measured after projection to physical
ordinary integers.  Repeated labels add to same physical column.

## 7. Revised whole-anchor frontier

The open product-truncated option is no longer a joint mass/capacity question.  Harmonic mass is
closed by `(17)`.  Exact remaining theorem is

`PRODUCT-TRUNCATED-E3-LOCAL-LAYER-UNIT-CARLESON-AND-SEAM`:

1. prove interval-uniform lower token density at square-root scale for same product-truncated
   allocations;
2. prove matching upper law for incoming squarefree \(\omega=s\) layer with factorial constants;
3. combine them with `(17)` to obtain column ceiling \(1+o(1)\), not a polylogarithm;
4. prove normalized one-large-prime to friable seam flux for same kernel.

Reservoir harmonic entropy and critical displacement no longer conflict once truncation is done
after subset formation.  Fine physical incidence is sole whole-anchor obstruction.

## 8. Novelty and anti-theatre audit

- Proof is finite combinatorics plus first logarithmic moment; no probabilistic limit theorem is
  hidden in `(4)`.
- Mertens/PNT inputs in `(16)` already exist in project corpus.
- New knowledge is exact product-truncation lower bound and its cofinal Route E parameter regime.
- Result does not rename row normalization as Hall capacity.
- No literature search, computation, Lean edit, or Lean build was performed.
