# Gaussian Hilbert Fano-curvature conjecture

- **ID:** gaussian-hilbert-fano-curvature
- **Stage:** 1-in-progress
- **Type:** COMPETING CONJECTURES / ANTI-THEATRE AUDIT
- **Novelty:** `[CONJECTURE BEYOND SOTA]`; no discovery claim
- **Source:** failure-driven successor to the Gaussian Hilbert-metric SOTA foundation

## Exact frontier

Let (x_1,\ldots,x_N) be distinct points in a real Hilbert space and

\[
  K_X(t)_{ij}=\exp(-t\lVert x_i-x_j\rVert^2),\qquad t>0.
\]

The SOTA foundation gives a centroid-corrected positive Fock--Pluecker partition
function

\[
  Z_X(t)=\exp(2tE_X)\det K_X(t)=\sum_{n\ge0}c_n(X)t^n,
  \qquad c_n(X)\ge0.
\]

Under the degree law

\[
  \mathbb P_t(D=n)=\frac{c_n(X)t^n}{Z_X(t)},
\]

the classical partition identities give

\[
  \mathbb E_tD=t(\log Z_X)'(t),\qquad
  \operatorname{Var}_t(D)=t\frac d{dt}\mathbb E_tD.
\]

Consequently the uncorrected metric determinant has the exact Fano-curvature law

\[
  t^2(\log\det K_X)''(t)
   =\operatorname{Var}_t(D)-\mathbb E_tD.                 \tag{FC}
\]

The identity (FC) is a foundation connector, not by itself a novelty claim.

## Competing conjectures

### C1 -- complete-Bernstein scale law

`[FALSE]`.  Conjecture that ((\log\det K_X)'\) is completely monotone for every
finite Hilbert configuration.

For three equidistant points, after writing (q=e^{-u}),

\[
 \det K=(1-q)^2(1+2q),\qquad
 \frac d{du}\log\det K=\frac{6q^2}{(1-q)(1+2q)}=:h(u).
\]

Every positive completely monotone function is log-convex.  Here

\[
 (\log h)''(u)=\frac{q}{(1-q)^2}-\frac{2q}{(1+2q)^2},
\]

which is negative for all sufficiently small positive (q), since division by (q)
has limit (1-2=-1).  Thus (h) is not completely monotone.  The killing mechanism
is the odd-cycle term in the three-point determinant, not a numerical counterexample.

### C2 -- sub-Poisson coherent-volume law

`[SURVIVES PRELIMINARY ATTACK]`.  For every finite family of distinct points,

\[
  \operatorname{Var}_t(D)\le \mathbb E_tD                 \tag{SP}
\]

for all (t>0).  Equivalently,

\[
  (\log\det K_X)''(t)\le0.                                \tag{LC}
\]

This says that antisymmetrizing coherent states suppresses total Fock-number noise
below the Poisson level at every scale.  It is not a consequence of positivity of the
coefficients of (Z_X): arbitrary positive graded partition functions can be
super-Poisson.

### C3 -- compressed-annihilator defect law

`[ACTIVE CONJECTURE]`.  Let (H_0\) be the finite-dimensional span of the centered
configuration and let \(\mathcal F_s(H_0)\) be its symmetric Fock space.  At scale
\(t\), let \(S_t\) be the span of the exponential vectors

\[
  \varepsilon(\sqrt{2t}\,x_i),
\]

and let (P_t) be the orthogonal projection onto (S_t).  For an orthonormal basis

\(e_1,\ldots,e_d\) of (H_0), compress the annihilation operators:

\[
  A_r(t)=P_ta(e_r)P_t\big|_{S_t},\qquad
  Q_t=\sum_{r=1}^d A_r(t)^*A_r(t).
\]

The coherent-state span is invariant under every annihilation operator, and the
Slater determinant moment formula plus the canonical commutation relations give

\[
 \mathbb E_tD-\operatorname{Var}_t(D)
  =\operatorname{tr}(Q_t^2)
    -\sum_{r,s=1}^d\lVert A_r(t)A_s(t)\rVert_{\mathrm{HS}}^2.       \tag{AD}
\]

The conjecture is that the right-hand side of (AD) is nonnegative for every finite
coherent-state span.  The stronger rigidity form asserts that it is positive whenever
\(N>1\) and the points are distinct.

This representation absorbs the obstruction that killed C1: odd cycles may destroy
all-order complete monotonicity, while (AD) asks for one exact second-order defect and
identifies the operator quantity that must carry its sign.

## Dependency-closed derivation of (AD)

Let \(\mathcal N\) be the one-particle number operator on symmetric Fock space and
let \(\mathrm d\Gamma(\mathcal N)\) be its lift to the (N)-fold exterior power.
The normalized exterior product of any orthonormal basis of (S_t) has the same degree
law as the normalized Fock--Pluecker expansion.  The standard Slater formulas give

\[
 \mathbb E_tD=\operatorname{tr}(P_t\mathcal NP_t),\qquad
 \operatorname{Var}_t(D)
 =\operatorname{tr}(P_t\mathcal N(1-P_t)\mathcal NP_t).    \tag{S}
\]

Write each annihilator in blocks for
\(\mathcal F_s(H_0)=S_t\oplus S_t^\perp\):

\[
 a_r=\begin{pmatrix}A_r&B_r\\0&C_r\end{pmatrix}.
\]

The zero lower-left block is annihilation invariance.  From
\([a_r,a_s^*]=\delta_{rs}I\), the upper-left block is

\[
 B_rB_s^*=\delta_{rs}I+A_s^*A_r-A_rA_s^*.                 \tag{CCR}
\]

Also

\[
 (1-P_t)\mathcal NP_t=\sum_r B_r^*A_r.
\]

Taking its Hilbert--Schmidt norm squared, inserting (CCR), and using
\(A_rA_s=A_sA_r\) gives

\[
 \operatorname{Var}_t(D)
 =\operatorname{tr}Q_t
   +\sum_{r,s}\lVert A_rA_s\rVert_{\mathrm{HS}}^2
   -\operatorname{tr}(Q_t^2).
\]

Finally \(\operatorname{tr}Q_t=\mathbb E_tD\), proving (AD).

## Hostile audit

- **Known parent theory:** Schoenberg infinite divisibility, coherent-state Gram
  matrices, symmetric Fock space, Cauchy--Binet/Pluecker expansions, Slater determinant
  moment formulas, and the canonical commutation relations are all established.
- **Not enough:** determinant monotonicity from Oppenheim--Schur, multiplicative
  log-convexity of the corrected determinant, and abstract mean/variance identities do
  not decide the sign in (SP).
- **Exact falsifier:** one coherent-state span with
  \(\operatorname{tr}(Q_t^2)<\sum_{r,s}\lVert A_rA_s\rVert_{HS}^2\).
- **Normalization attacks passed:** common translation changes the degree law by an
  independent Poisson displacement and leaves the Fano defect unchanged; ambient
  isometries only rotate the annihilation tuple; repeated points are excluded because
  the determinant and normalized exterior state vanish.
- **Small exact models passed:** two points reduce to the odd coherent state; regular
  simplices and Cartesian products factor into sub-Poisson components.  These checks
  are symbolic sanity checks, not evidence of truth.
- **Literature killing boundary:** any theorem proving log-concavity of
  \(t\mapsto\det(A^{\circ t})\) for all infinitely divisible correlation matrices, or
  the defect inequality (AD) for finite coherent-kernel spans, makes C2/C3 rediscovered.

## Failed commutator-square shortcut and positive survivor

`[FALSIFIED]`.  Pairwise commutativity does **not** turn (AD) into one half of a
sum of squared mixed commutators.  Put

\[
 R_t=\sum_r A_rA_r^*,\qquad
 \mathcal C_t=\sum_{r,s}\lVert[A_r,A_s^*]\rVert_{\mathrm{HS}}^2.
\]

Direct trace expansion, using only (A_rA_s=A_sA_r), gives the exact identity

\[
 \operatorname{tr}(Q_t^2)-
   \sum_{r,s}\lVert A_rA_s\rVert_{\mathrm{HS}}^2
 =\frac12\mathcal C_t+
   \frac12\bigl(\operatorname{tr}(Q_t^2)-\operatorname{tr}(R_t^2)\bigr). \tag{RC}
\]

The omitted row--column asymmetry term need not vanish.  On 
\(\mathbb R^3\), the commuting pair

\[
 A_1=E_{12},\qquad A_2=E_{13}
\]

has every product (A_rA_s=0), while

\[
 Q=E_{22}+E_{33},\qquad R=2E_{11},\qquad
 \operatorname{tr}(Q^2)=2,\quad \operatorname{tr}(R^2)=4,
 \quad \mathcal C=6.
\]

Thus the left side of (RC) is (2), whereas 
\(\mathcal C/2=3\).  This is an exact symbolic counterexample, not a numerical
test.  It kills the arbitrary-commuting-tuple square law and shows that
commutativity alone is the wrong representation.

`[PAPER-PROVED]` positive survivor: (RC) is the exact decomposition exposed by
the failure.  Its mathematical content is that the Fano defect consists of a
manifest mixed-commutator energy plus a signed imbalance between the column
energy (Q) and row energy (R).  The identity is parent matrix algebra and is
not a novelty claim; it will be formalised only if it is needed by the final
coherent-state theorem.

### C4 -- coherent row--column compensation law

`[CONJECTURE]`.  For annihilation compressions of a finite span of distinct
coherent states, the negative row--column imbalance can never consume the full
mixed-commutator energy:

\[
 \operatorname{tr}(R_t^2)-\operatorname{tr}(Q_t^2)
 < \mathcal C_t                                                     \tag{CC}
\]

whenever (N>1).  By (RC), (CC) is equivalent to strict sub-Poissonity, but its
representation is stronger scientifically: it identifies the exact compensation
mechanism that arbitrary commuting tuples lack.  The (E_{12},E_{13}) obstruction
does not apply because coherent restrictions are jointly diagonalizable with a
strictly positive coherent Gram matrix and arise from a common CCR dilation; the
nilpotent counterexample has neither property.

### C5 -- finite annihilation-invariant subspace law

`[STRONGER FRONTIER CONJECTURE]`.  Let `S` be any finite-dimensional subspace of a
symmetric Fock space that is invariant under every annihilation operator, let `P` be its
orthogonal projection, and let `N` be the number operator.  Then

\[
 \operatorname{tr}\bigl((P\mathcal NP)^2\bigr)
 \ge \operatorname{tr}\bigl(P(\mathcal N^2-\mathcal N)P\bigr).       \tag{AI}
\]

For a coherent span, the two sides of (AI) are respectively
`tr(Q_t^2)` and `sum_{r,s} ||A_r A_s||_HS^2`, so (AI) implies C2--C4.
Unlike C4, it is closed under collisions of coherent points: the limiting spaces contain
exponential jets and, at a total collision, derivative-invariant polynomial spaces.

This is not a cosmetic generalization.  It proposes that the sign is owned by finite
annihilation invariance itself, not by diagonalizability of the coherent compression.  The
graded polynomial case has zero number variance and the one-mode case is the proved
self-commutator square.  Neither boundary proves the multivariable statement.

**Exact falsifier:** a finite-dimensional joint-annihilation-invariant subspace for which

\[
 \operatorname{tr}\bigl(P\mathcal N(1-P)\mathcal NP\bigr)
   >\operatorname{tr}(P\mathcal NP).
\]

The likely proof or failure mechanism is a finite Koszul/CCR curvature identity on the
annihilation complex.  Merely citing negative dependence of Slater determinants is insufficient:
the number observable has unbounded integer weights, and generic projection determinantal
processes can be super-Poisson for such weighted statistics.

#### Hostile two-branch inverse-system test

Let `M,L >= 1` and, in the two-mode polynomial Fock space, take the derivative-invariant
subspace

\[
 S_{M,L,\lambda}=\operatorname{span}
 \{1,x,\ldots,x^{M-1},y,\ldots,y^{L-1},x^M+\lambda y^L\}.
\]

Its determinant-line vector has exactly two orthogonal homogeneous components.  If

\[
 B=\frac{M(M-1)+L(L-1)}2,
\]

their degrees are `B+M` and `B+L`.  Thus this family deliberately creates a degree gap
`|M-L|`, the simplest mechanism that could make a graded law super-Poisson.  At the scale
where the two components have equal probability,

\[
 \mathbb ED=\frac{M^2+L^2}{2},\qquad
 \operatorname{Var}(D)=\frac{(M-L)^2}{4},
\]

and hence

\[
 \mathbb ED-\operatorname{Var}(D)=\frac{(M+L)^2}{4}>0.
\]

At arbitrary component probability `p`, the variance is
`p(1-p)(M-L)^2`; the forced lowering-chain base degree keeps it below the mean.
This exact family therefore does not prove (AI), but it eliminates sparse two-degree support
as an easy counterexample and identifies a candidate mechanism: annihilation invariance charges
every large degree gap by the full lowering chains beneath it.

Trying to correlate several such gaps exposes the second constraint.  If a `k`-dimensional
top space is the graph of a coupling between low- and high-degree channels, its determinant-line
wedge contains the intermediate exterior powers of that coupling.  An invertible coupling cannot
have all intermediate exterior powers vanish.  Thus decomposability forces mixed Pluecker terms
and prevents `k` separate degree jumps from masquerading as one two-atom jump with quadratic
variance.  The emerging proof target is therefore a joint **lowering-chain/Pluecker variance
bound**, not an abstract DPP inequality and not pairwise matrix commutativity.

#### Failed arbitrary-commuting-tuple strengthening

`[FALSE]`.  A tempting strengthening was that (AI) might hold for every finite commuting
matrix tuple.  Write

\[
 Q=\sum_iA_i^*A_i,\qquad R=\sum_iA_iA_i^*.
\]

For a commuting tuple, cyclicity gives

\[
 \sum_{i,j}\lVert A_iA_j\rVert_{\mathrm{HS}}^2=\operatorname{tr}(QR),
\]

and direct expansion gives the useful parent identity

\[
 \sum_{i,j}\lVert[A_i,A_j^*]\rVert_{\mathrm{HS}}^2
   =\lVert Q-R\rVert_{\mathrm{HS}}^2.                         \tag{MC}
\]

Neither identity forces the sign of
`tr(Q^2)-tr(QR)`.  There is an exact symmetric-module counterexample.  On the
degree-at-most-two symmetric module over a `d`-dimensional space, choose an orthonormal
monomial basis and commuting lowering maps whose degree-one-to-vacuum weight is `a` and whose
degree-two-to-degree-one radial weight is `b` (square channels have the canonical factor
`sqrt 2`).  The column energy is diagonal.  Summing once over the `d` degree-one vectors and
once over the `d(d+1)/2` quadratic vectors gives

\[
 \operatorname{tr}(Q^2)-\sum_{i,j}\lVert A_iA_j\rVert_{\mathrm{HS}}^2
 =d a^4+d(d+1)b^2(2b^2-a^2).                              \tag{RT}
\]

Taking `d=8`, `a=2`, and `b=1` makes (RT) equal

\[
 8\cdot16+8\cdot9(2-4)=-16.
\]

Thus commutativity, nilpotence, a symmetric grading, and the Pluecker condition still do not
own the desired sign.  The counterexample is not a standard-Fock invariant subspace: its radial
renormalisation omits the transverse annihilation channels that any actual Fock-space metric
completion must carry.

#### Positive survivor -- quadratic graph completion

`[PAPER-PROVED]`.  Let `E,W` be finite-dimensional real Hilbert spaces, let
`T subset Sym^2(E)` have dimension `m`, and let `L : T -> W` be arbitrary.  Inside the
symmetric Fock space over `E direct-sum W`, consider

\[
 S_L=\mathbb R\Omega\oplus E\oplus\{q+Lq:q\in T\}.
\]

This is invariant under every annihilation operator.  Annihilation in an `E` direction lowers
the quadratic component into `E`; annihilation in a `W` direction lowers the correction `Lq`
directly into the vacuum.  These latter maps are precisely the completion channels absent from
the false weighted-tuple model.

Conversely, every nonzero annihilation-invariant polynomial subspace of maximal degree at most
two has this form after taking `E` to be its linear symbol, `T` its quadratic symbol, removing
lower terms from a section, and putting the residual linear correction in `W=E^perp`.  Thus this
is the complete quadratic stratum, not a chosen model.

Under degree dilation by `sqrt t`, the vacuum contributes `1`, the `E` block contributes
`t^e`, and the graph block has Gram operator

\[
 t^2I+tL^*L=t(tI+L^*L).
\]

Consequently its determinant-line partition is

\[
 Z_L(t)=t^{e+m}\det(tI+L^*L)
       =t^{e+m}\prod_{j=1}^m(t+\lambda_j),                 \tag{GC}
\]

where the nonnegative `lambda_j` are the eigenvalues of `L^*L`.  Its degree law is therefore a
deterministic baseline `e+m` plus independent Bernoulli variables with

\[
 p_j(t)=\frac{t}{t+\lambda_j}.
\]

Hence

\[
 \mathbb E_tD-\operatorname{Var}_t(D)
   =e+m+\sum_{j=1}^m p_j(t)^2>0                            \tag{GCF}
\]

whenever `e+m>0`.  This proves (AI) for every quadratic annihilation-invariant polynomial
subspace, a genuinely multivariable and arbitrarily non-graded universal stratum.  The exact
proof and its formalisation boundary are recorded in
`2-fully-proven/gaussian-hilbert-quadratic-graph-completion.md`.

## Proven frontier base case

`[PAPER-PROVED]`.  If the affine span of the configuration has dimension one, there is
only one compressed annihilator `A_t`.  Then `Q_t=A_t^*A_t` and `R_t=A_tA_t^*` have
the same squared trace, so the row--column anomaly in (RC) vanishes.  Consequently

\[
 -t^2(\log\det K_X)''(t)
   =\frac12\lVert[A_t,A_t^*]\rVert_{\mathrm{HS}}^2>0
\]

for every distinct configuration with `N > 1`.  Strictness follows because the coherent
eigenvectors have distinct real eigenvalues but nonzero pairwise inner products, whereas
distinct eigenspaces of a normal operator are orthogonal.  The dependency-closed proof is
recorded in `2-fully-proven/gaussian-hilbert-line-commutator-curvature.md`.

This is a genuine failure-driven boundary theorem, not a proof of C2: affine dimension
two is the first place where the signed row--column term can survive.

## `[OPEN CORE]`

Prove or refute the stronger invariant-subspace law (AI).  At minimum, prove or refute its
simple-spectrum coherent specialization

\[
 \operatorname{tr}\!\left(\sum_r A_r^*A_r\right)^2
 \ge \sum_{r,s}\lVert A_rA_s\rVert_{\mathrm{HS}}^2        \tag{OC}
\]

for the jointly diagonalizable commuting tuple obtained by compressing the annihilation
operators to a finite span of distinct coherent states.  Equivalently, prove (CC) by
using the coherent Gram geometry and the common CCR dilation.  Pairwise commutativity
alone is now known to be too coarse.  A counterexample to (AI) that is not a coherent span
must be tested under simple-spectrum perturbation before it kills C2.

No Lean formalization of C2/C3 is permitted before (OC) is closed on paper and the
equivalence-level literature audit is repeated.

## Literature audit log

- Horn's infinitely divisible matrix theory and Schoenberg's Hilbert-distance
  characterization own the positive-semidefinite Hadamard semigroup.
- Oppenheim--Schur determinant inequalities own monotonicity and additive-scale
  supermultiplicativity.
- Flat Gaussian RBF determinant asymptotics own the small-scale polynomial-rank order.
- Coherent-state Gram characterizations own the Fock realization.
- Searches through Gaussian-process log determinants, Hadamard powers, infinitely
  divisible correlation matrices, coherent-state Gram determinants, and sub-Poisson
  photon statistics located these parent theories but no source for (SP), (AD), or (OC).
  This is a preliminary search boundary, not a priority proof.

## Log

- 2026-07-19 -- C1 killed exactly by the equilateral three-point family.
- 2026-07-19 -- extracted (FC), reduced C2 to the coherent-span operator defect (OC),
  and made C3 the active failure-driven conjecture.
- 2026-07-19 -- falsified the tempting half-commutator-square shortcut, extracted the
  exact row--column decomposition (RC), and replaced the arbitrary commuting-tuple
  representation by the coherent compensation conjecture (CC).
- 2026-07-19 -- strengthened the frontier to finite annihilation-invariant subspaces and
  attacked it with a two-branch inverse system.  The intended sparse-degree counterexample
  instead produced the exact positive margin `(M+L)^2/4`, exposing lowering-chain cost as a
  possible sign mechanism.
- 2026-07-19 -- killed the arbitrary commuting-tuple strengthening by the exact eight-mode
  radial degree-two counterexample, then restored the missing standard-Fock completion channels
  and proved the quadratic graph completion law (GC)--(GCF).
