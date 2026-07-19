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

## `[OPEN CORE]`

Prove or refute

\[
 \operatorname{tr}\!\left(\sum_r A_r^*A_r\right)^2
 \ge \sum_{r,s}\lVert A_rA_s\rVert_{\mathrm{HS}}^2        \tag{OC}
\]

for the jointly diagonalizable commuting tuple obtained by compressing the annihilation
operators to a finite span of distinct coherent states.  The claim is not made for an
arbitrary commuting tuple unless that stronger statement is separately proved.

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
