# Rank-one Schur--Gaussian curvature law

- **ID:** rank-one-schur-gaussian-curvature-law
- **Stage:** 3-formalized
- **Type:** FAILURE-DRIVEN UNIVERSAL MATRIX / KERNEL LAW
- **Source:** `gaussian-hilbert-dimension-sandwich-law.md`
- **Scientific status:** `[FORMALIZED] [SEARCH NONCOLLISION] [PRIORITY UNVERIFIED]`
- **Statement:** Schur multiplication of an arbitrary positive-definite matrix by a
  one-dimensional Gaussian semigroup has a log-concave determinant, with an exact
  self-commutator curvature and equality classification.

## Exact claim

Let `I` be finite, let `C=(C_ij)` be a real positive-definite matrix, and let
`a=(a_i)` be arbitrary real labels.  Put

\[
 H_t(i,j)=C_{ij}e^{t a_i a_j},\qquad
 K_t(i,j)=C_{ij}e^{-t(a_i-a_j)^2}\qquad(t\ge0).
\]

Let `D=diag(a_i)`, let `R_t=H_t^{1/2}`, and define the square-root similarity

\[
 A_t=R_t D R_t^{-1}.
\]

The proposed **rank-one Schur--Gaussian curvature law** is

\[
 \boxed{\quad
 -{d^2\over dt^2}\log\det H_t
 ={1\over2}\lVert[A_t,A_t^T]\rVert_{HS}^2.\quad}       \tag{SGI}
\]

Since

\[
 K_t=\operatorname{diag}(e^{-ta_i^2})\,H_{2t}\,
      \operatorname{diag}(e^{-ta_i^2}),
\]

the metric/covariance form is

\[
 \boxed{\quad
 -{d^2\over dt^2}\log\det K_t
 =2\lVert[A_{2t},A_{2t}^T]\rVert_{HS}^2\ge0.\quad}     \tag{SGD}
\]

Thus `t -> log det K_t` is concave on the nonnegative half-line for every positive-definite
background `C`.  Equality at a scale is equivalent to

\[
 [A_t,A_t^T]=0
 \quad\Longleftrightarrow\quad
 DH_t=H_tD
 \quad\Longleftrightarrow\quad
 C_{ij}=0\text{ whenever }a_i\ne a_j.                  \tag{EQ}
\]

In particular, if every entry of `C` is nonzero and the labels are not all equal, the
concavity is strict at every scale.

## Geometric and kernel consequence

Let `x_1,...,x_N` be distinct points and let `M_0` be any positive-semidefinite background
Mahalanobis metric for which the background Gaussian Gram is positive definite.  For a linear
functional `v`, vary only its weight:

\[
 M_t=M_0+t\,v\otimes v,
 \qquad
 G_t(i,j)=e^{-\lVert x_i-x_j\rVert_{M_t}^2}.
\]

Then `G_t=C hadamard [e^{-t(a_i-a_j)^2}]`, with
`C_ij=e^{-||x_i-x_j||_(M_0)^2}` and `a_i=v(x_i)`.  Hence

\[
 \boxed{\qquad t\longmapsto\log\det G_t\text{ is concave}.\qquad} \tag{ARD}
\]

This gives coordinate-wise global concavity of the Gaussian-kernel log-volume under every
rank-one positive-semidefinite metric update, in any ambient dimension.  It is not implied by
joint concavity: the formalized degree-five configuration proves that ordinary concavity fails
for suitable higher-rank directions.

## Dependency-closed paper proof

### 1. Positivity at every scale

For `t>=0`, the matrix `E_t=[exp(t a_i a_j)]` is positive semidefinite by its symmetric-Fock
power series.  More precisely, `E_t=J+P_t`, where `J` is the all-ones matrix and `P_t` is the
sum of the positive-semidefinite homogeneous powers of positive degree.  Therefore

\[
 H_t=C\mathbin\circ E_t=C+C\mathbin\circ P_t.
\]

The Schur product theorem makes the second summand positive semidefinite.  A positive-definite
matrix plus a positive-semidefinite matrix is positive definite, so `H_t>0`.  The diagonal
factorization in the statement then also gives `K_t>0`.

### 2. Exact determinant curvature

Entrywise differentiation gives

\[
 H_t'=DH_tD,\qquad H_t''=D^2H_tD^2.                    \tag{1}
\]

The standard determinant differential formula consequently gives

\[
 {d^2\over dt^2}\log\det H_t
 =\operatorname{tr}(H_t^{-1}D^2H_tD^2)
  -\operatorname{tr}((H_t^{-1}DH_tD)^2).               \tag{2}
\]

Write `H_t=R_t^2` with `R_t` positive definite and put `A_t=R_tDR_t^{-1}`.  Cyclicity of trace,
symmetry of `R_t`, and `(A_t)^2=R_tD^2R_t^{-1}` give the two literal conversions

\[
 \operatorname{tr}(H_t^{-1}D^2H_tD^2)=\lVert A_t^2\rVert_{HS}^2,
 \qquad
 \operatorname{tr}((H_t^{-1}DH_tD)^2)
 =\operatorname{tr}((A_t^TA_t)^2).                     \tag{3}
\]

For every finite real matrix `A`, cyclicity also gives the unconditional identity

\[
 \lVert[A,A^T]\rVert_{HS}^2
 =2\left(\operatorname{tr}((A^TA)^2)-\lVert A^2\rVert_{HS}^2\right). \tag{4}
\]

Substitution of (3)--(4) into (2) proves (SGI), with no limiting or spectral hypothesis.

### 3. Gaussian distance form

Taking determinants in the displayed diagonal factorization of `K_t` yields

\[
 \log\det K_t=-2t\sum_i a_i^2+\log\det H_{2t}.          \tag{5}
\]

The first term is affine.  Differentiating (5) twice and applying (SGI) at `2t` proves (SGD).
The nonpositive second derivative proves global concavity; continuity supplies the endpoint
`t=0`.

### 4. Equality and strictness

The curvature vanishes exactly when `A_t` is normal.  It is similar to the real diagonal matrix
`D`, so all its eigenvalues are real.  A real normal matrix with real spectrum is symmetric.
Thus equality is equivalent to `A_t=A_t^T`.  Multiplication on the left and right by `R_t`
shows

\[
 A_t=A_t^T\quad\Longleftrightarrow\quad H_tD=DH_t.      \tag{6}
\]

Conversely, if `H_t` commutes with `D`, functional calculus makes `R_t=H_t^(1/2)` commute with
`D`, so `A_t=D` and equality holds.  Finally,

\[
 (DH_t-H_tD)_{ij}=(a_i-a_j)C_{ij}e^{t a_i a_j}.
\]

The exponential factor never vanishes, proving (EQ).  If every `C_ij` is nonzero, equality
therefore forces all labels to coincide, which proves the stated strictness.

## Hostile audit boundary

1. `[LITERATURE]` The Schur product theorem, entrywise exponential positivity, ordinary
   concavity of `log det` on the positive cone, and the finite self-commutator trace identity
   are parent results.  None alone supplies (SGI), because `t -> K_t` is not an affine path in
   the positive cone.
2. `[LOCAL-RESEARCH]` `gaussian-hilbert-dimension-sandwich-law.md` proves rank-`r` power
   concavity for a pure Gaussian direction.  It does not allow an arbitrary background `C`,
   and for `r>1` it does not give ordinary concavity.
3. `[LOCAL-RESEARCH]` `exists_finiteGaussianDistanceGram_positiveLogDetCurvature` is the sharp
   hostile boundary: the proposed ordinary concavity cannot extend from rank one to unrestricted
   positive-semidefinite directions.
4. Searches for Schur-product Gaussian semigroup determinant concavity, Hadamard-power
   determinant curvature, rank-one conditionally-positive generators, Gaussian taper
   determinants, and anisotropic Gaussian-kernel log-determinants found positivity, static
   determinant inequalities, numerical log-determinant work, and general matrix-cone
   concavity, but no statement equivalent to (SGI)--(EQ).  This is only search noncollision;
   priority remains unverified.
5. The practical ARD interpretation is a genuine consequence only if the theorem retains
   arbitrary `C>0` and proves global concavity.  Restricting `C` to the all-ones matrix would
   merely recover the already formalized Hilbert-line law.

## Lean formalization

The exact theorem surface is compiled in
`GaloisForLFunctions.HilbertMetric.RankOneSchurGaussianConcavity` and exported through the
`GaloisForLFunctions.HilbertMetric` umbrella.  It includes:

- the reusable real-normal eigenvector orthogonality lemmas;
- `matrixSqrtSimilarity_selfCommutator_eq_zero_iff_diagonal_blocks`, the positive-Gram
  normality-rigidity parent theorem;
- `rankOneSchurExponential_logDet_secondDerivative_eq`, the literal identity `(SGI)`;
- `rankOneSchurGaussian_logDet_secondDerivative_eq`, the literal identity `(SGD)`;
- `rankOneSchurGaussian_logDet_concaveOn`, global concavity on `Set.Ici 0`;
- both literal zero-curvature iff block theorems and both strict-curvature corollaries; and
- `rankOneSchurGaussian_sharpUniversalLaw`, packaging `(SGI)`, `(SGD)`, global concavity, and
  the complete equality classification.

The direct leaf check and direct Hilbert umbrella check pass.  The final narrow audit
`lake build GaloisForLFunctions.HilbertMetric` completed all 2820 jobs successfully.  Explicit
`#print axioms` checks of ten headline declarations report only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or project axiom occurs.  Repository lint recognizes the new module as
reachable.  Its nonzero exit is caused only by eight unrelated concurrently owned modules missing
from the `RHTower`, `HTGeometry`, or Hilbert umbrellas; none is imported by this theorem.

## External frontier checked

- M. S. Floater, *Bounds on the determinant of an exponential matrix*, arXiv:2603.19900:
  static determinant bounds, not scale curvature.
- D. Guillot, A. Khare, and B. Rajaratnam, *Complete characterization of Hadamard powers
  preserving Loewner positivity, monotonicity, and convexity*, arXiv:1311.1581: entrywise-power
  preservers in Loewner order, not determinant curvature along the present Schur semigroup.
- K. Dong et al., *Scalable Log Determinants for Gaussian Process Kernel Learning*,
  arXiv:1711.03481: computation of log determinants and derivatives, not a shape theorem.
- H. Feldmeier and J. Schnack, *Molecular Dynamics for Fermions*, arXiv:cond-mat/0001207:
  antisymmetrized Gaussian/coherent Slater states as an established application class, without
  the curvature bound.

## Gates

- [x] 0 -> 1: exact claim, parent boundary, higher-rank falsifier, and initial SOTA map recorded
- [x] 1 -> 2: dependency-closed paper proof and hostile equality audit
- [x] 2 -> 3: exact unconditional Lean theorem, direct checks, axiom audit, and final module build
- [ ] 3 -> 4: independent priority audit and demonstrated general-journal significance

## Log

- 2026-07-20 -- extracted the arbitrary-background rank-one law from the failure of ordinary
  concavity in higher-rank Gaussian directions; isolated self-commutator curvature as the exact
  proposed positive survivor.
- 2026-07-20 -- closed the dependency-complete trace proof, arbitrary-background positivity,
  Gaussian diagonal gauge, and exact equality/strictness classification; promoted to Stage 2
  without changing the conservative priority label.
- 2026-07-20 -- formalized the exact positive-Gram normality rigidity, both curvature identities,
  the complete equality classification, strictness, and global Gaussian concavity; direct leaf and
  umbrella checks, the 2820-job Hilbert module build, and the explicit axiom audit passed.  Kept
  priority and general-journal significance unverified.
