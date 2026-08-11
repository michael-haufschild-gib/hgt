# Total-variation conflict coloring and observer-width law

- **ID:** ULF-FKT-TVCC-1
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** For any finite family of pairwise total-variation tasks, lossless deterministic
  observers are exactly proper colorings of the source sign-conflict graph.  Minimal observer range
  is therefore its chromatic number, and every improper coloring has an explicit positive loss
  witness.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [MECHANISM NOT OBJECT]
  [OBSERVER RESOURCE LAW] [LEAN-PROVED] [NOT RH]

## 1. Setup

Let `X` be a nonempty finite source and `J` a finite task set.  Task `j` consists of two real
profiles `u_j,v_j:X->R`; in the statistical application they are nonnegative finite measures.  Put

\[
 d_j(x)=u_j(x)-v_j(x).
 \tag{TVCC.1}
\]

For an observer `kappa:X->K`, define pushforward by fibre summation and define

\[
 \operatorname{TV}(u,v)=\frac12\sum_x|u(x)-v(x)|.
 \tag{TVCC.2}
\]

The observer is **lossless for the task family** when

\[
 \operatorname{TV}(\kappa_!u_j,\kappa_!v_j)
 =\operatorname{TV}(u_j,v_j)
 \quad(j\in J).
 \tag{TVCC.3}
\]

Define the simple **task-conflict graph** `G_d` on `X` by

\[
 x\sim_d y
 \quad\Longleftrightarrow\quad
 \exists j\in J,\ d_j(x)d_j(y)<0.
 \tag{TVCC.4}
\]

The strict inequality makes this relation symmetric and irreflexive.  It records exactly which
source atoms must remain distinguishable for at least one declared task.

## 2. Exact fibre-loss formula

For task `j` and observer value `k`, put

\[
 P_{j,k}=\sum_{\kappa(x)=k}\max(d_j(x),0),\qquad
 N_{j,k}=\sum_{\kappa(x)=k}\max(-d_j(x),0).
 \tag{TVCC.5}
\]

### Theorem 2.1

For every task,

\[
 \boxed{
 \operatorname{TV}(u_j,v_j)-
 \operatorname{TV}(\kappa_!u_j,\kappa_!v_j)
 =\sum_{k\in K}\min(P_{j,k},N_{j,k}).}
 \tag{TVCC.6}
\]

Consequently the loss is nonnegative.  It vanishes exactly when every observer fibre contains no
positive and negative values of `d_j` simultaneously.

### Proof

On a fixed fibre, `sum |d_j|=P_{j,k}+N_{j,k}` and
`|sum d_j|=|P_{j,k}-N_{j,k}|`.  Hence half their difference is

\[
 \frac12(P_{j,k}+N_{j,k}-|P_{j,k}-N_{j,k}|)
 =\min(P_{j,k},N_{j,k}).
\]

Summing over fibres proves `(TVCC.6)`.  A minimum of two nonnegative finite sums is zero exactly
when at least one sum is zero.  Such a sum is zero exactly when all its nonnegative summands are
zero.  QED.

This is also the exact fibre formula and total-variation identity of ULF-FKT-OD-1, applied
simultaneously to a prescribed task family.

## 3. Lossless observation is graph coloring

### Theorem 3.1 — conflict-coloring equivalence

For a deterministic observer `kappa:X->K`, the following are equivalent.

1. `kappa` is lossless for every task in `J`.
2. No observer fibre contains an edge of `G_d`.
3. `kappa` is a proper coloring of `G_d` by the labels in `K`.

### Proof

By Theorem 2.1, losslessness for task `j` says that no fibre contains one point where `d_j` is
positive and another where it is negative.  Requiring this for every `j` says exactly that no
fibre contains a pair satisfying `(TVCC.4)`.  This is precisely the proper-coloring condition.
QED.

### Corollary 3.2 — minimal observer resource

The least number of observer values used by a lossless deterministic observer is

\[
 \boxed{\chi(G_d).}
 \tag{TVCC.7}
\]

Indeed, every lossless observer is a proper coloring, and every proper coloring is a lossless
observer by Theorem 3.1.  Equivalently, for every positive integer `q`, a lossless observer
`X->Fin q` exists exactly when `G_d` is `q`-colorable.

This is not the minimal-sufficient-statistic theorem for an entire statistical experiment.  It is
the exact resource theorem for preserving only the declared finite family of pairwise
total-variation tasks.  A richer task doctrine can produce a strictly finer statistic.

## 4. Local certificate for every failure

### Theorem 4.1

Suppose `kappa(x)=kappa(y)` and some task `j` has `d_j(x)d_j(y)<0`.  After swapping `x,y` if
necessary, let `a=d_j(x)>0` and `b=-d_j(y)>0`.  Then

\[
 \boxed{
 \operatorname{TV}(u_j,v_j)-
 \operatorname{TV}(\kappa_!u_j,\kappa_!v_j)
 \ge \min(a,b)>0.}
 \tag{TVCC.8}
\]

### Proof

In their common fibre, `P_{j,kappa(x)}>=a` and `N_{j,kappa(x)}>=b`.  Its contribution in
`(TVCC.6)` is therefore at least `min(a,b)`.  Every other fibre contribution is nonnegative.  QED.

Thus graph noncolorability is not merely a counting obstruction.  Every monochromatic conflict
edge carries a task-labelled quantitative certificate.

## 5. Hostile universality theorem

### Theorem 5.1 — arbitrary graph realization

Every finite simple graph `H` is a task-conflict graph.

### Proof

Take `X=V(H)`.  Use one task for every ordered adjacent pair `(x,y)`.  Set

\[
 u_{x,y}=\delta_x,\qquad v_{x,y}=\delta_y.
 \tag{TVCC.9}
\]

Its signed difference is `+1` at `x`, `-1` at `y`, and zero elsewhere, so it creates exactly the
undirected conflict edge `{x,y}`.  The union over all ordered adjacent pairs is exactly `H`.  QED.

Therefore positivity does not force conflict graphs to be perfect, chordal, matroidal, Helly,
bounded-chromatic, or otherwise special.  Any such structure must come from additional source
formation laws, not from positive observation itself.

## 6. Cofinal width law and compactness boundary

For a sequence of finite task systems with conflict graphs `G_n`, a fixed `q`-valued observer can
be lossless at every stage only if `chi(G_n)<=q` for every `n`; conversely each stage admits a
`q`-valued lossless observer whenever this inequality holds.  Hence unbounded chromatic number is
an exact **finite observer-width obstruction**.

For an infinite conflict graph, the de Bruijn--Erdos compactness theorem supplies the sharp
combinatorial boundary: for finite `q`, global `q`-colorability is equivalent to `q`-colorability
of every finite subgraph.  Thus if all finite conflict systems are uniformly `q`-colorable but no
admitted global observer exists, the obstruction cannot be bare combinatorics.  It lies in a
separate topology, regularity, measurability, equivariance, or coherence requirement imposed on
the observer.

The finite theorem above, including the stagewise cofinal width law
(`stagewise_observerWidthAtMost_iff_conflictColorable`), is Lean-certified in
`HTGeometry.ConstitutiveTVConflictColoring`.  The de Bruijn--Erdos sentence is a direct citation
of the classical compactness theorem, not a claim of this programme.

## 7. Mechanism-level consequence

Lossless observation has two independent obstruction axes:

1. **conflict width:** finite source distinctions demand enough observer colors;
2. **admission:** an abstract coloring may fail to be continuous, measurable, equivariant,
   coherent across stages, or available in the chosen completion.

This separation is the field-level gain.  A route that says only “the observer loses information”
has not identified its mechanism.  One must determine whether it lacks enough distinguishable
states or whether an abstractly adequate observer is rejected by its analytic/source doctrine.

## 8. Parent boundary

The ingredients are classical:

- equality cases of total-variation data processing and sufficient statistics;
- graph coloring and chromatic number;
- de Bruijn--Erdos compactness for finite graph coloring.

The theorem is classified as a bridge.  Its role is to expose one exact mechanism and one sharp
boundary, not to claim a historically new graph or statistics theorem.

Primary parent:

- N. G. de Bruijn and P. Erdos, *A colour problem for infinite graphs and a problem in the theory
  of relations*, Nederl. Akad. Wetensch. Proc. Ser. A 54 (1951), 371--373,
  <http://www.math-inst.hu/~p_erdos/1951-01.pdf>.

## 9. Exact scope

- finite source and task family for Theorems 2.1--5.1;
- deterministic observers;
- preservation of prescribed pairwise total variations, not arbitrary statistical decisions;
- no claim that every corpus observer is positive or deterministic;
- no RH implication and no source-selected arithmetic observer;
- no identification of chromatic width with action, curvature, complexity, or physical length.

## Log

- 2026-08-11 -- stagewise cofinal width law certified; card promoted to stage 3.
