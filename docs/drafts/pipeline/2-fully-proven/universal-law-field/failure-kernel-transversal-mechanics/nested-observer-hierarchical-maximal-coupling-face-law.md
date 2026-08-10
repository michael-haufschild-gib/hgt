# Nested-observer hierarchical maximal-coupling face law

- **ID:** ULF-FKT-HMCF-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** positive-overlap-defect calculus; positive survivor of ULF-FKT-MOBIUS-NOGO
- **Statement:** nested finite observer partitions admit one coupling simultaneously maximizing
  agreement at every level; its collision strata are exactly the successive overlap-defect masses.
- **Status:** [PROVED HERE] [DEPENDENCY-CLOSED] [MECHANISM NOT ROUTE]
  [CLASSICAL INGREDIENTS] [NOVELTY UNVERIFIED] [TWO-LEVEL CORE LEAN-PROVED]
  [ARBITRARY FINITE CHAIN LEAN-PENDING] [NOT RH]

## 1. Setup

Let `X` be finite.  Let `mu,nu:X->[0,infinity)` be probability profiles.  Let

\[
  \mathcal P_0\preceq\mathcal P_1\preceq\cdots\preceq\mathcal P_N
\]

be partitions of `X`, where every block of `P_j` lies in a block of `P_{j+1}`.  Write

\[
  E_j=\{(x,y):x,y\text{ lie in the same }\mathcal P_j\text{-block}\}
\]

and

\[
  A_j=\sum_{B\in\mathcal P_j}\min\{\mu(B),\nu(B)\}.
\]

Put `A_{-1}=0`.  A coupling is a nonnegative matrix `gamma(x,y)` with row marginal `mu` and column
marginal `nu`.

## 2. The theorem

### Theorem 2.1 (hierarchical simultaneous maximality)

There exists a coupling `gamma_*` such that

\[
  \gamma_*(E_j)=A_j\qquad(0\le j\le N).
\tag{HMCF.1}
\]

For every coupling `gamma`,

\[
  \gamma(E_j)\le A_j.
\tag{HMCF.2}
\]

Hence the simultaneous-maximizer set

\[
  \mathfrak F=\{\gamma:\gamma(E_j)=A_j\text{ for every }j\}
\tag{HMCF.3}
\]

is a nonempty exposed face of the transport polytope.  Every `gamma in F` has the forced collision
stratum masses

\[
  \gamma(E_0)=A_0,
  \qquad
  \gamma(E_j\setminus E_{j-1})=A_j-A_{j-1},
  \qquad
  \gamma((X\times X)\setminus E_N)=1-A_N.
\tag{HMCF.4}
\]

If `f_j:X->P_j` is the quotient observer, then

\[
  A_j=1-\operatorname{TV}((f_j)_!\mu,(f_j)_!\nu).
\tag{HMCF.5}
\]

Consequently `A_j-A_{j-1}` is exactly the distinguishability lost in the observer step
`P_{j-1}->P_j`, equivalently the total mass of the binary false-overlap defect from ULF-FKT-OD-1.

## 3. Proof

### 3.1 Universal upper bound

For any block `B` and any coupling,

\[
 \gamma(B\times B)\le \mu(B),\qquad
 \gamma(B\times B)\le \nu(B).
\]

Therefore `gamma(B x B)<=min(mu(B),nu(B))`.  Summing over the disjoint blocks of `P_j` proves
`(HMCF.2)`.

### 3.2 Recursive construction

Start at `P_0`.  Inside each block `B`, couple total mass

\[
  m_B=\min\{\mu(B),\nu(B)\}
\]

using the scaled product coupling

\[
  \gamma_B(x,y)=
  \begin{cases}
  \mu(x)\nu(y)/\nu(B),&\mu(B)\le\nu(B),\ \nu(B)>0,\\
  \mu(x)\nu(y)/\mu(B),&\nu(B)<\mu(B),\ \mu(B)>0,\\
  0,&m_B=0.
  \end{cases}
\]

This removes the smaller marginal total from `B`.  Thus the residual marginals on each `P_0`
block are **one-sided**: at most one of the two residual totals is nonzero.

Inductively suppose all agreement mass through `P_{j-1}` has been inserted and every
`P_{j-1}` block is residual-one-sided.  In a parent block `C in P_j`, let `alpha_C,beta_C` be the
remaining `mu` and `nu` masses in `C`.  Insert a scaled product coupling of total
`min(alpha_C,beta_C)` between the residual measures in `C`.

No newly inserted pair lies in `E_{j-1}`: such a pair would lie in one child block, but each child
has residual mass on at most one side.  Hence the new mass lies in `E_j\E_{j-1}`.  After it is
inserted, the parent residuals are one-sided.  This closes the induction.

At level `j`, the total mass inserted in a parent `C` equals the increase between the sum of child
minima and the parent minimum.  Summing over parents telescopes to `A_j-A_{j-1}`.  After level `N`,
couple the remaining equal total marginal masses arbitrarily.  Parent one-sidedness puts all of
that final mass outside `E_N`.  This constructs `gamma_*` and proves `(HMCF.1)` and `(HMCF.4)`.

### 3.3 Exposed-face statement

On the transport polytope, each `gamma -> gamma(E_j)` is linear and bounded above by `A_j`.
Therefore the maximizers of

\[
  \gamma\longmapsto\sum_{j=0}^N\gamma(E_j)
\]

are exactly the couplings attaining every individual upper bound.  They are `F`, so `F` is a
nonempty exposed face.

### 3.4 Total-variation identity

For probability vectors `a,b`,

\[
  \sum_z\min(a_z,b_z)
  =\frac12\sum_z(a_z+b_z-|a_z-b_z|)
  =1-\operatorname{TV}(a,b).
\]

Apply this to the block masses of `P_j` to prove `(HMCF.5)`.  The exact serial overlap theorem then
identifies `A_j-A_{j-1}` with the step defect mass.

## 4. Sharp necessity of hierarchy

Nestedness cannot be replaced by an arbitrary family of observers.  Let

\[
 X=\{1,2,3,4\},\quad
 \mu=\tfrac12(\delta_1+\delta_4),\quad
 \nu=\tfrac12(\delta_2+\delta_3).
\]

For

\[
 \mathcal P=\{\{1,2\},\{3,4\}\},\qquad
 \mathcal Q=\{\{1,3\},\{2,4\}\},
\]

maximal `P`-agreement uniquely forces `1->2` and `4->3`, whereas maximal `Q`-agreement uniquely
forces `1->3` and `4->2`.  The maximal faces are disjoint.  Compatibility is therefore a genuine
order law, not a generic property of many coarse-grainings.

## 5. Mechanism interpretation

The primitive is not a scalar curvature.  It is a **consensus face** carrying witnesses compatible
with every stage of a nested observer history.  Scalar total-variation losses are its face-stratum
masses.  This yields five route-independent laws:

1. observer agreement capacities are monotone under coarsening;
2. hierarchy makes the capacities jointly realizable by one history witness;
3. successive information losses are positive collision strata;
4. incomparable observers can be contextually incompatible even when every scalar capacity exists;
5. witness enrichment restores positivity after scalar Möbius irreducibility fails.

## 6. Hostile audit and parents

- Maximal coupling, transport polytopes, total-variation contraction, and hierarchical coupling
  constructions are classical ingredients.
- Multi-distribution divergences and multiclass testing are established; product-additive
  multi-distribution divergences have strong recent classification results.
- Möbius inversion and positivity by categorical/orthogonal enrichment are established themes.
- No claim of external novelty or RH leverage is made.  Corpus-level advance is the exact welding
  of observer defect composition to a simultaneous coupling face and collision filtration.
- The theorem does not cover signed profiles, nonnested observers, infinite tightness, physical
  clocks, or source selection.

Primary nearby sources:

- Duchi--Khosravi--Ruan, *Multiclass Classification, Information, Divergence, and Surrogate Risk*,
  <https://arxiv.org/abs/1603.00126>;
- Balsubramani, *All you need is log: classifying multi-distribution divergences*,
  <https://arxiv.org/abs/2606.27349>;
- Moulines--Priouret--Roueff, *Maximal agreement couplings*,
  <https://arxiv.org/abs/1608.01511>;
- *Orthogonal Möbius inversion and nonnegative persistence*,
  <https://arxiv.org/abs/2311.06870>.

## 7. Lean target

`HTGeometry.ConstitutiveHierarchicalMaximalCoupling` now certifies:

- finite profiles, couplings, observer capacities, and agreement mass;
- universal capacity upper bound;
- an explicit coupling simultaneously maximal for two nested observer levels.

The arbitrary finite-chain induction, full collision-stratum package, and incompatible-partition
countermodel remain Lean-pending.  They do not count as certified results.

No theorem is Stage 3 until direct elaboration, lint, axiom audit, umbrella wiring, and final module
build pass.

## Log

- 2026-08-10 — theorem and hostile scope closed on paper; Lean pending.
- 2026-08-10 — two-level simultaneous-maximality core elaborates cleanly in Lean; arbitrary finite
  chain remains paper-only.
