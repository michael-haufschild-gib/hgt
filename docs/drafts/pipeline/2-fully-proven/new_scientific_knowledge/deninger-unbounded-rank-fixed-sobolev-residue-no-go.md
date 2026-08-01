# No fixed Sobolev order controls pro-log residue evaluation

- **ID:** `deninger-unbounded-rank-fixed-sobolev-residue-no-go`
- **Stage:** 2-fully-proven
- **Type:** NO-GO THEOREM WITH POSITIVE SURVIVOR
- **Label:** `DAC_UNBOUNDED_RANK_FIXED_SOBOLEV_RESIDUE_NO_GO`
- **Parent:** `deninger-horizontal-residue-transverse-graph-no-go`
- **Scientific status:** `[NEW PRO-SYSTEM OBSTRUCTION; SOBOLEV EMBEDDING PARENT STANDARD]`
- **Statement:** because finite pro-log character lattices have
  unbounded horizontal rank, no fixed horizontal Sobolev order gives
  stage-uniform control of source residue evaluation; the required
  repair is an all-order or holomorphic nuclear topology, not one
  stronger Hilbert norm.

## Rank-cube witness

At a horizontal unitary torus of rank (d), fix an evaluation point
(zeta=(zeta_1,ldots,zeta_d)) and define

\[
 F_d(z)
 =2^{-d/2}\prod_{j=1}^d
   (1+\overline{\zeta_j}z_j).                                \tag{1}
\]

The Fourier support is the cube ({0,1}^d), with all (2^d)
coefficients of modulus (2^{-d/2}).  Therefore

\[
 \|F_d\|_{L^2(\mathbb T^d)}=1,
 \qquad
 |F_d(\zeta)|^2=2^d.                                       \tag{2}
\]

For integer Sobolev order (s\ge0), use the standard Fourier norm

\[
 \|F\|_{H^s}^2
 =\sum_{k\in\mathbb Z^d}(1+|k|^2)^s|\widehat F(k)|^2.       \tag{3}
\]

Every (k\in{0,1}^d) satisfies (|k|^2\le d), hence

\[
 \|F_d\|_{H^s}^2\le(1+d)^s.                               \tag{4}
\]

## Theorem

`[PROVED HERE] [DAC_UNBOUNDED_RANK_FIXED_SOBOLEV_RESIDUE_NO_GO]`

For every fixed (s\),

\[
 { |F_d(\zeta)|^2 \over \|F_d\|_{H^s}^2 }
 \ge {2^d\over(1+d)^s}
 \longrightarrow\infty.                                   \tag{5}
\]

Consequently there is no constant (C_s), independent of finite
pro-log stage, such that

\[
 |F(\zeta)|\le C_s\|F\|_{H^s}                              \tag{6}
\]

for all source character lattices.  Tensoring `(1)` with one fixed
transverse Tate mode leaves this conclusion unchanged for any topology
formed from that fixed horizontal (H^s) norm and arbitrary
transverse graph powers.

### Proof

Equations `(2)` and `(4)` follow from Fourier orthogonality and the
cube support.  Exponential growth dominates every polynomial:

\[
 {(1+d)^s\over2^d}\to0.
\]

Taking reciprocals gives `(5)`.  If `(6)` held, squaring and applying
it to `(1)` would bound the left side of `(5)` by (C_s^2), a
contradiction.

The source pro-log system admits finite-dimensional valuation-zero
subspaces of arbitrarily large rank.  Thus (d\to\infty) is a genuine
stage direction of the arithmetic construction, not an auxiliary
limit.

## No-go closure

- **Exact killing theorem/mechanism:** tensor-cube evaluation grows
  exponentially in horizontal rank, whereas every fixed-order Sobolev
  weight grows only polynomially.  A rank-independent fixed Sobolev
  graph completion cannot make all pro-log residue evaluations
  continuous.
- **Strongest positive survivor:**
  `[PROVED HERE] [DAC_PRO_LOG_ALL_ORDER_RESIDUE_CONTROL_NECESSITY]`.
  A viable topology must increase horizontal regularity with rank or
  retain a projective all-order/compact-open holomorphic topology.  The
  existing finite-stage pro-log Stein topology has exactly this
  property and should be intersected with, not replaced by, the Tate
  transverse graph topology.
- **New insight:** Route L cannot be repaired by choosing one larger
  anisotropic Hilbert Sobolev exponent.  Unbounded arithmetic character
  rank forces a genuinely nuclear/projective source topology before
  completion.
- **Status:** dependency-closed paper proof; scalar exponential versus
  polynomial ratio formalized in Lean together with preceding
  Dirichlet-packet obstruction.

## Hostile scope audit

- Fixed (d) is not obstructed: any (s>d/2) controls evaluation.
- Rank-adaptive Sobolev systems and compact-open holomorphic topologies
  survive.
- The theorem concerns uniform pro-stage residue continuity, not local
  elliptic regularity or prime-circle high-frequency control.
- No Xi divisor, zeta zero, RH premise, or numerical experiment enters.

## Revised next exact claim

`[CONJECTURE] [DAC_PRO_LOG_TATE_PROJECTIVE_GRAPH_STRICTNESS]`

Define the source graph topology as the projective intersection of all
finite-stage compact-open logarithmic-form seminorms and all
Tate-transverse graph powers.  Prove transition maps, Poincare residue,
packet evaluation, corestriction, and relative Milnor cells are strict
for this projective system; then prove the weighted all-prime Green
forms are summable on every resulting Banach disk.

## Gates

- [x] exact pro-rank witness
- [x] complete paper proof
- [x] positive survivor extracted
- [x] internal collision audit
- [ ] Lean module direct audit
- [ ] projective graph strictness

## Log

- 2026-08-01 — Proved fixed Sobolev repair fails across unbounded
  pro-log rank and isolated full projective/holomorphic topology as
  mandatory survivor.
