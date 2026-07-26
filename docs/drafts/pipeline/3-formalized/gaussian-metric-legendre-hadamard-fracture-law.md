# Gaussian metric Legendre--Hadamard fracture law

- **ID:** `gaussian-metric-legendre-hadamard-fracture-law`
- **Stage:** `3-formalized`
- **Type:** UNIVERSAL HILBERT-METRIC / MATRIX-CONE LAW
- **Source:** `rank-one-schur-gaussian-curvature-law.md` and the compiled degree-five
  Gaussian-curvature counterexample
- **Scientific status:** `[PAPER-PROVED] [SEARCH NONCOLLISION] [PRIORITY UNVERIFIED]
  [GENERAL-JOURNAL SIGNIFICANCE UNVERIFIED]`
- **RH status:** `[NO DIRECT RH IMPACT]`; this is a metric/kernel theorem and currently has no
  `RHTower` consumer.

## Exact law

Let `I` be finite, let `x_i` be points in a finite-dimensional real Hilbert space, let `C` be a
background kernel, and define for every symmetric metric tensor `M`

\[
 G_C(M)_{ij}=C_{ij}\exp\!\left(-(x_i-x_j)^T M(x_i-x_j)\right).
\]

At any `M` for which `G_C(M)>0`, every symmetric rank-one line has the exact curvature law

\[
 \boxed{\quad
 {d^2\over dt^2}\log\det G_C(M+t,v v^T)
 =-2\left\|[A_{v,t},A_{v,t}^T]\right\|_{HS}^2\le0.
 \quad}                                                     \tag{LH}
\]

Here `a_i=v^T x_i`, and `A_(v,t)` is the positive-square-root similarity from the sharp
rank-one Schur--Gaussian law, evaluated at twice the metric parameter.  Consequently

\[
 M\longmapsto\log\det G_C(M)
\]

is rank-one concave on every positive-Gram component of the metric cone.  If every entry of the
background Gram is nonzero, equality in `(LH)` occurs exactly when the projection `v^T x_i` is
constant on the finite configuration.

This rank-one concavity does **not** extend to ordinary concavity.  The formalized degree-five
configuration supplies an injective finite Euclidean family `X` for which

\[
 \boxed{\qquad
 {d^2\over dt^2}\log\det
   [\exp(-t\lVert x_i-x_j\rVert^2)]\bigg|_{t=1}>0.
 \qquad}                                                    \tag{FR}
\]

The direction in `(FR)` is the identity metric on a space of dimension greater than one, hence a
higher-rank direction.  Together `(LH)` and `(FR)` are the **Gaussian metric
Legendre--Hadamard fracture law**: Gaussian kernel log-volume is concave along every rank-one
metric perturbation while failing to be concave on the full metric cone.

## Finite Hilbert-extension form

The theorem can be stated without choosing ambient metric coordinates.  Let
`y_i` be distinct finite Hilbert feature vectors and let `a_i` be an arbitrary additional scalar
feature.  Put

\[
 K_t(i,j)=\exp\!\left(-\lVert y_i-y_j\rVert^2-t(a_i-a_j)^2\right).
\]

Then `K_t>0` for `t>=0`, and

\[
 t\longmapsto\log\det K_t
\]

is globally concave, strictly so when the added feature is nonconstant.  Appending the coordinate
`sqrt(t) a_i` is precisely a rank-one extension of the squared Hilbert metric.  Conversely, a
Mahalanobis update `M -> M+t vv^T` has this form with `a_i=v^T x_i`.

## Dependency-closed proof

1. The metric identity

   \[
   (x_i-x_j)^T(M+t vv^T)(x_i-x_j)
   =(x_i-x_j)^TM(x_i-x_j)+t(a_i-a_j)^2
   \]

   converts the metric line exactly into Schur multiplication by the one-dimensional Gaussian
   semigroup.
2. Apply `rankOneSchurGaussian_logDet_secondDerivative_eq` to obtain `(LH)`, and apply
   `rankOneSchurGaussian_logDet_concaveOn` for global line concavity.
3. The sharp zero-curvature theorem says equality is equivalent to vanishing background entries
   between distinct `a`-levels.  Gaussian entries never vanish, so an injective finite Gaussian
   background has equality exactly when `a` is constant.
4. `exists_finiteGaussianDistanceGram_positiveLogDetCurvature` supplies `(FR)` with an injective
   Euclidean configuration and a nonzero determinant at unit scale.  A twice differentiable
   concave function cannot have positive second derivative at an interior point, so full metric
   concavity is impossible.

No limiting, numerical, genericity, RH, or unproved spectral assumption is used.

## Anti-theatre boundary

1. Positive definiteness of Gaussian kernels, the Schur product theorem, ordinary concavity of
   `log det` on the positive cone, and the equivalence of `C^2` rank-one convexity with the
   Legendre--Hadamard condition are parent mathematics.
2. The determinant itself is a classical rank-one-affine but nonconvex function.  That generic
   example does not imply `(LH)`, the exact self-commutator curvature, or the Gaussian
   higher-rank fracture `(FR)`.
3. ARD literature uses “log-determinant concavity” for covariance matrices affine in variance
   hyperparameters.  The present metric path is entrywise exponential and is not affine in the
   metric parameter.
4. Searches for `rank-one concavity Gaussian kernel determinant`, `Legendre--Hadamard Gaussian
   kernel log determinant`, `Mahalanobis Gaussian log determinant curvature`, and their matrix
   variants found general elasticity criteria, Gaussian positivity, static determinant
   inequalities, and bandwidth optimization, but no equivalent theorem.  This is search
   noncollision, not priority evidence.
5. Merely renaming coordinatewise ARD concavity as rank-one concavity would be theatre.  The
   scientific content retained here is the invariant metric-tensor statement, the exact
   nonnormality curvature, strict equality classification, and the compiled higher-rank
   counterexample establishing a genuine separation.

## Publication gate

The fracture law has a broader cross-domain surface than the Schur-path theorem alone: metric
learning, Gaussian-process entropy, D-optimal kernel volume, matrix rank-one convexity, and
nonnormality all meet in one exact identity.  It is not yet certified for a general scientific
journal.  Stage 4 requires:

- an independent priority audit spanning kernel learning and the calculus of variations;
- a stability or quantitative consequence of the self-commutator curvature, not only its sign;
- a worked metric-learning or Gaussian-process consequence that changes an existing analysis;
- manuscript-level treatment of the distinction between symmetric rank-one concavity,
  quasiconcavity, and full concavity.

## Gates

- [x] 0 -> 1: invariant metric statement, exact rank-one connector, and higher-rank falsifier
- [x] 1 -> 2: dependency-closed proof and hostile parent boundary
- [x] 2 -> 3: unconditional Lean metric connector, direct checks, axiom audit, and final module build
- [ ] 3 -> 4: independent priority and general-journal significance audit

## Lean certificate

File: `formal/GaloisForLFunctions/HilbertMetric/GaussianMetricRankOneFracture.lean`
(imported by `GaloisForLFunctions.HilbertMetric`).  Every theorem below builds clean and
`#print axioms` returns exactly `propext, Classical.choice, Quot.sound`.

| Card item | Lean name |
|---|---|
| finite Hilbert-extension Gram `K_t(i,j) = exp(-‖y_i-y_j‖² - t(a_i-a_j)²)` | `gaussianMetricRankOneExtensionGram` |
| the metric line is Schur multiplication by the one-dimensional Gaussian semigroup | `gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath` |
| positive Gram component of the metric cone | `finiteGaussianDistanceGram_posDef_of_injective_of_pos`, `finiteGaussianDistanceGram_posDef_iff_injective_of_pos` |
| **(LH)** exact self-commutator curvature | `gaussianMetricRankOneExtension_logDet_secondDerivative_eq` |
| rank-one concavity of `M ↦ log det G_C(M)` | `gaussianMetricRankOneExtension_logDet_concaveOn` |
| equality exactly when the projection `v^T x_i` is constant | `gaussianMetricRankOneExtension_logDet_secondDerivative_eq_zero_iff_constant` |
| strict negativity for a nonconstant added feature | `gaussianMetricRankOneExtension_logDet_secondDerivative_lt_zero` |
| **(FR)** higher-rank fracture, injective degree-five configuration | `exists_finiteGaussianDistanceGram_positiveLogDetCurvature` |
| **(LH) + (FR)** packaged fracture law | `gaussianMetricRankOneConcavity_and_higherRankFracture` |

The proof route is exactly the dependency-closed proof of this card: the metric identity turns the
rank-one line into the Schur-Gaussian path, `rankOneSchurGaussian_logDet_secondDerivative_eq` and
`rankOneSchurGaussian_logDet_concaveOn` supply (LH) and line concavity, the sharp zero-curvature
theorem gives the equality classification (Gaussian entries never vanish), and the compiled
degree-five configuration supplies (FR).

## Log

- 2026-07-20 -- extracted the invariant metric-tensor form of the rank-one Schur law and combined
  it with the compiled positive-curvature Gaussian configuration.  Promoted only to Stage 2;
  novelty priority and general-journal significance remain unverified.
- 2026-07-26 -- stage audit: the Lean metric connector, equality classification, and higher-rank
  falsifier are all present and axiom-clean.  Card moved to `3-formalized`; the Stage 3 -> 4
  priority and significance audit remains open.
