# Route E forward-interval Hall reduction

- **ID:** `ROUTE-E-FORWARD-INTERVAL-HALL-001`
- **Stage:** 3-formalized
- **Formalized companion:** `./route-e-forward-interval-hall-reduction-formalized.md`
- **Type:** THEOREM (paper) / EXACT SOURCE REDUCTION
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** general Hall-cut necessity is formalized in
  `MobiusBoundaryOppositeSignTransport.lean`; the full interval equivalence `(1)`–`(2)` and the
  sharp quarter threshold `(7)` are formalized in
  `HTGeometry/ForwardWindowHallMatching.lean`

## Theorem

Let \(E,T\) be finite subsets of \(\mathbb Z\), let \(H\ge1\), and join \(e\in E\) to
\(q\in T\) when

\[
e<q\le e+H.
\tag{1}
\]

There is an injection \(f:E\to T\) satisfying `(1)` for every \(e\) if and only if, for every
integer interval \(I=[a,b]\),

\[
\#(E\cap I)\le \#\bigl(T\cap(a,b+H]\bigr).
\tag{2}
\]

Thus the exponentially large family of Hall subset inequalities collapses exactly to consecutive
physical intervals for a one-sided equal-window relation.

## Proof

Necessity is immediate.  Every neighbor of a point in \(E\cap[a,b]\) lies in
\(T\cap(a,b+H]\), so an injective assignment forces `(2)`.

For sufficiency, let \(S\subseteq E\).  Form

\[
\mathcal U_S=\bigcup_{s\in S}(s,s+H].
\]

Decompose this finite union into its pairwise-disjoint connected interval components.  A component
has the form

\[
(a_j,b_j+H],
\]

where \(a_j\) and \(b_j\) are respectively the least and greatest source points whose windows
belong to that component.  The sources in one component form a subset
\(S_j\subseteq E\cap[a_j,b_j]\), and its full neighbor set is exactly

\[
N(S_j)=T\cap(a_j,b_j+H].
\]

By `(2)`,

\[
\#S_j\le\#(E\cap[a_j,b_j])
\le\#N(S_j).
\]

Different components have disjoint neighbor sets, so summing gives
\(\#S\le\#N(S)\).  Hall's marriage theorem supplies the required injection.

## Cofactor-token specialization

Restrict the cofactor-amplified construction to
\[
t\in[T_0/2,T_0],\qquad T_0=U^{2\eta}.
\]
All resulting windows have comparable length
\[
H\asymp U^{1/2+\eta}(\log U)^{1.55}.
\]
For either parity, every interval of length \(H\) contains
\[
D\gg_\eta
\frac{U^{1/2+\eta}}
     {(\log U)^{0.45}}
\]
physical targets.  Partitioning longer intervals into \(H\)-blocks gives target capacity
\[
\gg_\eta
D+\frac{|I|}{(\log U)^2}.
\tag{3}
\]

Consequently the following local exceptional-set estimate is a sufficient arithmetic source:
\[
\#(E_\sigma(U)\cap I)
\le c_\eta\left(
\frac{U^{1/2+\eta}}
     {(\log U)^{0.45}}
+\frac{|I|}{(\log U)^2}
\right)
\tag{4}
\]
for every integer interval \(I\), with \(c_\eta\) below the target constant in `(3)`.

There is also a sharp threshold for discarding local information.  Suppose only
\[
\#E_\sigma(U)\ll U^{1-\kappa+o(1)}
\tag{5}
\]
is known.  The trivial bounds
\(\#(E_\sigma\cap I)\le\min\{|I|,\#E_\sigma\}\) imply `(4)` for all \(I\) only if the
small-interval padding reaches the large-interval transition:
\[
U^{1/2+\eta}\ge U^{1-\kappa+o(1)},
\qquad\text{i.e.}\qquad
\eta+\kappa\ge\frac12.
\tag{6}
\]
Strict-half exceptional cost requires \(\eta<\kappa\).  An \(\eta\) satisfying both strict
inequalities exists exactly when
\[
\boxed{\kappa>\frac14.}
\tag{7}
\]
For \(\kappa\le1/4\), a single cluster of an admissible global size lies in the uncontrolled
interval range, so global cardinality alone cannot prove Hall.

## Hostile audit

- Global cardinality is only `(2)` for \(I\) equal to the whole scale and does not imply the
  intermediate interval inequalities unless the saving crosses the sharp quarter threshold
  `(7)`.
- Row degree is `(2)` only for singleton intervals and also does not imply matching.
- The reduction is classical convex-bipartite/Hall geometry; standalone novelty is not claimed.
  Its Route E value is that it turns the remaining co-degree problem into the explicit Carleson
  estimate `(4)`.
- Weighted Gibbs capacity follows with \(1+o(1)\) distortion on these \(H=o(U)\) windows; the
  exact weighted and co-moving sector versions remain on the parent card.

## Status

`[PROVED HERE; LEAN-CERTIFIED; CLASSICAL COMBINATORIAL CONTENT]`.  Route E source is reduced to `(4)` and its
weighted co-moving sector analogue for a genuinely identified exceptional vertex set.  The
separate ordinary-window signed defect current remains on the parent card.
