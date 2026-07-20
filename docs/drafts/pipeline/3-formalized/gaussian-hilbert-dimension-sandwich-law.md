# Gaussian Hilbert dimension-sandwich law

- **ID:** gaussian-hilbert-dimension-sandwich-law
- **Stage:** 3-formalized
- **Type:** CANDIDATE UNIVERSAL DIMENSION--CURVATURE LAW
- **Source:** `gaussian-hilbert-ccr-dimension-fluctuation-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED]
  [SEARCH NONCOLLISION] [PRIORITY UNVERIFIED]
  [GENERAL-JOURNAL SIGNIFICANCE UNVERIFIED]`
- **Statement:** The centroid-corrected Gaussian Gram volume of every finite Hilbert
  configuration is logarithmically convex in log bandwidth and logarithmically concave in the
  affine-dimension power of bandwidth.  Equivalently, the log-scale curvature of every
  rank-`d` positive-semidefinite Hadamard exponential determinant lies between zero and `d`
  times its log-scale slope.

## Metric statement

Let `X=(x_1,...,x_N)` be distinct points in a real Hilbert space.  Let `c` be their centroid,

\[
 E_X=\sum_i\lVert x_i-c\rVert^2
     ={1\over N}\sum_{i<j}\lVert x_i-x_j\rVert^2,
\]

and let `d>=1` be the dimension of their affine span.  For `t>0`, put

\[
 K_X(t)_{ij}=e^{-t\lVert x_i-x_j\rVert^2},
 \qquad Z_X(t)=e^{2tE_X}\det K_X(t),
 \qquad F_X(t)=\log Z_X(t).
\]

The proposed name for the exact theorem is the **Gaussian Hilbert dimension-sandwich law**:

\[
 \boxed{\quad
 s\longmapsto F_X(e^s)\text{ is convex},
 \qquad
 u\longmapsto F_X(u^{1/d})\text{ is concave}.
 \quad}                                                     \tag{DS}
\]

The second function is strictly concave when `N>1`.  Equivalently, if

\[
 C_X(t)=tF_X'(t),
\]

then

\[
 \boxed{\quad
 0\le tC_X'(t)\le dC_X(t).
 \quad}                                                     \tag{FD}
\]

Thus `C_X(t)` is nondecreasing while `C_X(t)/t^d` is nonincreasing.  For `a,b>0` and
`0<=theta<=1`, define

\[
 G_\theta(a,b)=a^{1-\theta}b^\theta,
 \qquad
 M_{d,\theta}(a,b)=((1-\theta)a^d+\theta b^d)^{1/d}.
\]

More strongly, with `u=t^d`, let

\[
 C=\sum_{i,j}\lVert A_iA_j^*-A_j^*A_i\rVert_{HS}^2,
 \qquad
 K=\sum_{i,j}\left\lVert
   dB_i^*A_j-\delta_{ij}\sum_kB_k^*A_k
 \right\rVert_{HS}^2.
\]

Then the pointwise curvature itself is the exact sum of squares

\[
 \boxed{\quad
 -d^3(d+1)u^2{d^2\over du^2}F_X(u^{1/d})=d^2C+K.
 \quad}                                                     \tag{PC}
\]

Thus power concavity is not obtained from a lossy estimate: it is the sign shadow of a rigidity
identity, and equality is exactly mixed normality plus pure-trace leakage.

Then (DS) is the two-sided interpolation law

\[
 \boxed{\quad
 Z_X(G_\theta(a,b))
 \le Z_X(a)^{1-\theta}Z_X(b)^\theta
 \le Z_X(M_{d,\theta}(a,b)).
 \quad}                                                     \tag{MI}
\]

The right inequality can be written without the centroid correction as

\[
 \det K_X(M_{d,\theta})\ge
 e^{-2E_X(M_{d,\theta}-(1-\theta)a-\theta b)}
 \det K_X(a)^{1-\theta}\det K_X(b)^\theta.                 \tag{KD}
\]

## Matrix and dimension-witness forms

The metric statement is equivalently a rank-sensitive law for entrywise matrix exponentials.
Let `A` be a real positive-semidefinite matrix of rank `d>=1`, assume no two columns of `A` are
equal, and put

\[
 H_A(t)=\exp^{\circ}(tA)=[e^{tA_{ij}}],
 \qquad \Phi_A(s)=\log\det H_A(e^s).
\]

Factoring `A` as a Gram matrix places its columns in `R^d`; the no-equal-columns condition is
exactly distinctness of those feature points.  The law becomes

\[
 \boxed{\qquad 0\le \Phi_A''(s)\le d\,\Phi_A'(s)\qquad(s\in\mathbb R).\qquad} \tag{DC}
\]

Consequently `u -> log det H_A(u^(1/d))` is concave on the positive half-line.  Conversely, at
every scale where `Phi_A'(s)>0`, the determinant curve itself gives the metric-only embedding
dimension witness

\[
 \boxed{\qquad {\Phi_A''(s)\over\Phi_A'(s)}\le \operatorname{rank}A.\qquad}   \tag{DW}
\]

For a centered Hilbert configuration with Gram matrix `A`, the corrected Gaussian determinant
is `Z_X(t)=det H_A(2t)`.  Thus (DC) is not an analogy or an application-layer wrapper: it is the
same theorem written entirely in matrix data or entirely in squared-distance data.  It also says
that the number Fano factor of the associated coherent Slater line is at most the number of
active Hilbert modes.

## Dependency-closed proof

Center the points and use the symmetric-Fock feature vectors
`epsilon(sqrt(2t)(x_i-c))`.  Their Gram matrix has determinant `Z_X(t)`.  Let `S_t` be their
finite span and let `P_t` be its orthogonal projection.  The normalized exterior product of an
orthonormal basis of `S_t` has an integer number-operator law `D_t` satisfying

\[
 C_X(t)=\mathbb E D_t,
 \qquad tC_X'(t)=\operatorname{Var}(D_t).                  \tag{1}
\]

Choose an orthonormal basis of the `d`-dimensional affine span and write the annihilation
operators in blocks relative to `S_t+S_t^perp`:

\[
 a_i=\begin{pmatrix}A_i&B_i\\0&C_i\end{pmatrix}.
\]

The coherent span is invariant under every annihilator.  Hence the `A_i` commute, and the
upper-left canonical commutation relations are

\[
 B_iB_j^*=\delta_{ij}I+A_j^*A_i-A_iA_j^*.                 \tag{2}
\]

Although `S_t^perp` may be infinite-dimensional, only the finite span of the ranges of the
maps `B_i^*:S_t->S_t^perp` occurs in (2), so the finite-matrix CCR
dimension--fluctuation theorem applies.  Its variables are exactly

\[
 E=\mathbb E D_t,
 \qquad V=\operatorname{Var}(D_t).
\]

It gives the stronger sum-of-squares identity

\[
 d(d+1)(dE-V)=d^2\sum_{i,j}\lVert A_iA_j^*-A_j^*A_i\rVert_{HS}^2
 +\sum_{i,j}\left\lVert
   dB_i^*A_j-\delta_{ij}\sum_kB_k^*A_k
 \right\rVert_{HS}^2.                                    \tag{3}
\]

Thus `0<=V<=dE`, proving (FD).  For `u=t^d`, the chain rule gives

\[
 {d^2\over du^2}F_X(u^{1/d})
 ={\operatorname{Var}(D_t)-d\mathbb ED_t\over d^2u^2}\le0,
\]

whereas

\[
 {d^2\over ds^2}F_X(e^s)=\operatorname{Var}(D_{e^s})\ge0.
\]

This proves (DS), and the defining inequalities for convexity and concavity give (MI) and (KD).

For strictness, vanishing of the first sum in (3) makes the commuting tuple `(A_i)` jointly
normal.  The coherent feature vectors are joint eigenvectors with joint eigenvalues
`sqrt(2t)(x_j-c)`.  Distinct points give distinct joint eigenvalues, so joint normality would make
the corresponding eigenspaces orthogonal.  Their coherent inner products are strictly positive,
a contradiction when `N>1`.  Hence `V<dE` and the power-scale concavity is strict.

## Anti-theatre and hostile audit

1. The left inequality in (MI), the positive Fock--Pluecker expansion, and the first inequality
   in (FD) are parent log-partition theory.  They are infrastructure, not the discovery claim.
2. Nonnegative graded coefficients alone do not imply `Var<=d Mean`; arbitrary positive
   partitions violate it.  The right inequality is supplied specifically by annihilation
   invariance plus the full CCR completion.
3. The compiled positive-curvature Gaussian counterexample does not falsify (DS).  It has
   `Var>Mean` but (3) still forces `Var<d Mean`; the centroid-corrected volume can be convex in
   ordinary bandwidth while remaining concave in `t^d`.
4. At `d=1`, (DS) reduces to ordinary concavity of `log Z_X(t)` and the exact
   self-commutator curvature law.  Affine dimension two is the first genuinely new power-scale
   regime.
5. The theorem is invariant under Hilbert isometries and common translations.  It depends on the
   ambient space only through the intrinsic affine dimension and the squared-distance matrix.
6. Exact searches across Gaussian-kernel bandwidth curvature, Hadamard-exponential determinants,
   power concavity, coherent-state number fluctuations, determinantal processes, complete
   log-concavity, and multivariable compressed shifts have not located (DS), (DC), (FD), (MI), or
   (3).  Search noncollision is not priority evidence; the result remains
   `[PRIORITY UNVERIFIED]`.
7. The closest direct determinant paper found is Michael Floater's March 2026 preprint *Bounds on
   the determinant of an exponential matrix* (arXiv:2603.19900).  It proves static upper and lower
   bounds and a univariate Gaussian corollary, but its searchable full text contains no
   convexity, concavity, derivative, rank/dimension, or fluctuation theorem.  This is adjacent
   SOTA, not a collision.
8. Other inspected parents are Sano's strict-positivity criterion for Hadamard exponentials,
   Schoenberg/Guella Gaussian positivity on Hilbert spaces, Barthelme--Usevich flat-limit
   determinant asymptotics, Alpay--Colombo--Diki--Sabadini's Gaussian-RBF/Fock correspondence,
   and Arveson's dimension-sensitive commutator theory.  None states the rank-sensitive
   determinant curvature inequality or the finite CCR sum-of-squares identity used here.
9. The exponent `d` is forced sharply by the finite CCR trace/traceless identity, but optimality
   within the smaller class of finite coherent spans is not yet proved.  The paper must say
   **CCR-sharp**, not **Gaussian-sharp**, until an extremizing sequence is constructed or a smaller
   universal coherent exponent is ruled out.

## Publication threshold

This has a substantially broader surface than the operator identity alone: it is a metric
inequality for every finite Hilbert configuration, simultaneously relevant to Gaussian kernels,
Hadamard exponentials, determinantal volumes, intrinsic-dimension witnessing, scale-space
geometry, and quantum number fluctuations.  The completed Hilbert connector removes the largest
internal proof-risk, and the 2026 adjacent paper shows that exact Gaussian/exponential determinant
bounds are an active topic.  General-journal significance is nevertheless not certified by
formal completeness or search noncollision.  Before promotion to Stage 4 the package still needs:

- an independent expert-level priority audit of the exact right-hand inequality in (MI), ideally
  including citation-network and non-English terminology checks;
- either Gaussian-sharpness of exponent `d`, or a quantitatively useful dimension-witness theorem
  showing that (DW) detects dimensions larger than one on a robust geometric class;
- a worked cross-domain consequence for kernel bandwidth design, D-optimal volume, or coherent
  quantum-number fluctuations that is not merely a restatement of (DC);
- a manuscript-level equality/stability analysis.  Strictness is paper-proved for more than one
  point, but the strict theorem and near-equality geometry are not yet Lean-formalized.

## Lean programme

- [x] Exact finite CCR sum-of-squares identity, dimension bound, and rigidity criterion:
  `HilbertMetric/CCRDimensionFluctuation.lean`.
- [x] Finite block-compression connector producing `IsCCRCompletion` from a commuting full CCR
  tuple and an invariant finite subspace.
- [x] Slater number mean/variance connector identifying the matrix `E,V` with the graded
  determinant law.
- [x] Generic twice-differentiable fluctuation-to-power-concavity theorem, exact curvature
  quotient, and log-scale convexity theorem.
- [x] Exact operator power-curvature sum of squares and combined CCR scale-sandwich theorem:
  `HilbertMetric/CCRPowerConcavity.lean`.
- [x] Strict positivity of every injective finite coherent Gram, including the coordinate-free
  separating-functional/Vandermonde argument.
- [x] Literal first- and second-log-determinant derivative connectors identifying slope with CCR
  mean and curvature with CCR number variance.
- [x] Exact Gaussian power-curvature sum-of-squares theorem and global log-scale convexity and
  dimension-power concavity.
- [x] Intrinsic arbitrary-real-Hilbert-space specialization through the finite centered span,
  with automatic positive affine dimension for at least two distinct points.

The compiled headline surface in `HilbertMetric/GaussianJetPositivity.lean` is:

- `gaussianCoherentLogScale_dimension_curvature_sumOfSquares_at` for (DC) with its exact defect;
- `gaussianDimensionPowerLogDetSecond_sumOfSquares` for (PC);
- `gaussianCoherentLogScale_logDet_convex`;
- `gaussianDimensionPowerLogDet_concaveOn`;
- `gaussianAffineDimension_pos_of_injective`;
- `gaussianCorrectedDimensionPowerLogDet_eq_rpow`, which identifies the formal power coordinate
  literally with `u ↦ log Z(u^(1/d))` on `u>0`;
- `gaussianCorrectedLogScale_convex_and_dimensionPower_concave_of_card_gt_one` for the
  nondegenerate universal Hilbert metric statement.

## Gates

- [x] 0 -> 1: exact metric statement, falsification boundary, and SOTA parent map recorded
- [x] 1 -> 2: dependency-closed Fock/CCR/calculus proof and strictness argument closed on paper
- [x] 2 -> 3: typed block, Slater, calculus, Gaussian metric, and intrinsic Hilbert connectors
  compile directly; the final HilbertMetric module build and explicit axiom audit pass
- [ ] 3 -> 4: priority audit plus Gaussian sharpness or a broad independent consequence

## Log

- 2026-07-20 -- extracted (DS)--(MI) from the formalized CCR dimension--fluctuation identity;
  closed the paper proof, strictness argument, hostile boundary, and conservative publication
  gate without making a priority or general-journal claim.
- 2026-07-20 -- formalized the full finite block connector, reciprocal-dimension chain rules,
  exact identity (PC), and the global operator scale-sandwich theorem.  Direct leaf checking
  passes; umbrella/final build evidence is deliberately deferred until the Gaussian connector is
  either closed or recorded as the exact remaining open core.
- 2026-07-20 -- closed the Gaussian connector: strict coherent-Gram positivity, the literal
  determinant-jet/CCR moment identities, the all-scale dimension-curvature sum of squares,
  global log-scale convexity, global dimension-power concavity, and the arbitrary-Hilbert-space
  centered-span specialization all pass direct Lean checking.
- 2026-07-20 -- hostile adjacent-SOTA pass found Floater's arXiv:2603.19900 on static determinant
  bounds but no scale-shape collision.  Reframed the discovery as the rank-sensitive
  Hadamard-exponential dimension-curvature law (DC), while retaining `[PRIORITY UNVERIFIED]` and
  `[GENERAL-JOURNAL SIGNIFICANCE UNVERIFIED]` until the sharpness/application gates are closed.
- 2026-07-20 -- final Stage-3 audit passed: `lake build GaloisForLFunctions.HilbertMetric`
  completed successfully, the direct HilbertMetric umbrella check passed, and the seven headline
  declarations report only `propext`, `Classical.choice`, and `Quot.sound`.  Repository-wide lint
  remains red only from unrelated reachability/large-file debt, not from a forbidden declaration
  or unclosed proof in this law.
