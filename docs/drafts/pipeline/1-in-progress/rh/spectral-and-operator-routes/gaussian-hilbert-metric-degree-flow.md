# Gaussian Hilbert-metric degree flow

- **ID:** gaussian-hilbert-metric-degree-flow
- **Stage:** 1-in-progress
- **Type:** SOTA FOUNDATION + CONJECTURE GENERATOR
- **Novelty:** `[REDISCOVERED FOUNDATION]`; no scientific-novelty claim
- **Source:** metric-first Hilbert-space research prompted by the 2026-07-19 universal-law goal
- **Statement:** The centroid-corrected determinant of every finite Gaussian distance matrix on a real Hilbert space is a nonnegative graded partition function.  Consequently its logarithmic bandwidth elasticity is a monotone mean Fock degree, its log-scale curvature is exactly a degree variance, and its flat endpoint is the cumulative polynomial-interpolation deficit of the metric configuration.

## Exact target

Let \(x_1,\ldots,x_N\) be a finite family in a real Hilbert space, let
\(c=N^{-1}\sum_i x_i\), and put
\[
  E_X=\sum_i\lVert x_i-c\rVert^2
      ={1\over N}\sum_{i<j}\lVert x_i-x_j\rVert^2.
\]
For \(t>0\), define the Gaussian distance matrix and corrected volume
\[
  K_X(t)_{ij}=e^{-t\lVert x_i-x_j\rVert^2},\qquad
  Z_X(t)=e^{2tE_X}\det K_X(t).
\]

After restricting to the finite-dimensional affine span and choosing coordinates,
let \(\alpha\in\mathbb N^d\) index monomials.  For each \(N\)-element set
\(B=\{\alpha_1,\ldots,\alpha_N\}\), put
\[
  w_X(B)={2^{\sum_{\alpha\in B}|\alpha|}\over
               \prod_{\alpha\in B}\alpha!}
          \det[x_i^\alpha]_{i,\alpha\in B}^{\,2},
  \qquad d(B)=\sum_{\alpha\in B}|\alpha|.
\]
The target law is
\[
  Z_X(t)=\sum_B w_X(B)t^{d(B)},\qquad w_X(B)\ge0.                 \tag{Fock--Pluecker}
\]
It implies all of the following metric statements.

1. **Three-scale law.**  For \(a,b>0\),
   \[
     \det K_X(\sqrt{ab})^2
       \le e^{2E_X(\sqrt a-\sqrt b)^2}
          \det K_X(a)\det K_X(b).                              \tag{TS}
   \]
2. **Degree-flow law.**  When the points are distinct, set
   \[
     C_X(t)=t{d\over dt}\log Z_X(t).
   \]
   Under the probability law
   \(\mathbb P_t(B)=w_X(B)t^{d(B)}/Z_X(t)\),
   \[
     C_X(t)=\mathbb E_t[d(B)],\qquad
     {dC_X\over d\log t}=\operatorname{Var}_t(d(B))\ge0.       \tag{DF}
   \]
3. **Flat endpoint.**  If
   \(h_m(X)\) is the rank of evaluation on polynomials of total degree at most
   \(m\), then
   \[
     \lim_{t\downarrow0}C_X(t)
       =\nu_X
       =\sum_{m\ge0}(N-h_m(X)),                                \tag{HF}
   \]
   the minimum total degree of a polynomial evaluation basis on \(X\).
4. **Origin-gauge law.**  If the Fock expansion is formed about an arbitrary
   origin \(a\), its partition function is exactly
   \[
     Z_{X,a}(t)=e^{2Nt\lVert a-c\rVert^2}Z_X(t),                \tag{CG}
   \]
   so the centroid is the unique coefficientwise-minimal translation gauge unless
   the configuration is a singleton.

The theorem is purely about finite metrics induced by real Hilbert space.  Its relationship
to the wider project is motivational: it turns a finite metric reporter into an exact,
scale-dependent complexity flow without asserting an HTGeometry or RHTower result.

## Gates

- [x] 0 -> 1: exact statement, metric normalization, parent boundary, falsifiers, and Lean programme recorded
- [ ] 1 -> 2: dependency-closed paper proof of (Fock--Pluecker), (TS), (DF), (HF), and (CG)
- [ ] 2 -> 3: exact unconditional Lean theorem surface, targeted checks, final module build, and axiom audit
- [ ] 3 -> 4: independent flat-kernel and algebraic-interpolation priority audit

## Parent theory and novelty boundary

### Established parents

- Gaussian kernels on Hilbert space and their strict positive definiteness are classical.
- Symmetric Fock feature expansions of \(e^{\langle x,y\rangle}\), Cauchy--Binet, and
  squared Pluecker coordinates are classical.
- Flat Gaussian RBF limits, multivariate Vandermonde blocks, determinant asymptotics,
  and polynomial interpolation are established; Barthelme--Usevich,
  *Spectral properties of kernel matrices in the flat limit* (SIAM J. Matrix Anal.
  Appl. 42 (2021), arXiv:1910.14067) is the closest located determinant parent.
- Tropicalizations of positive-definite principal minors and valuated matroid language are
  established and are not claimed as new.
- Log-convexity and mean/variance identities for an abstract nonnegative graded partition
  function are established parent mathematics.  The Lean parent layer is
  `GaloisForLFunctions.HilbertMetric.GradedPartition`.
- Schur positivity and Oppenheim's determinant inequality already imply monotonicity of
  `det K_X(t)` under increasing Gaussian inverse bandwidth.  Ordinary determinant
  monotonicity is therefore explicitly excluded from the novelty claim.

### Anti-theatre verdict

`[REDISCOVERED FOUNDATION]`.  Centroid correction, the Fock feature map, Cauchy--Binet,
positive Pluecker weights, and the mean/variance calculus for a graded partition function are
all classical ingredients.  Their assembly is useful SOTA infrastructure and gives a clean
metric theorem surface, but an exact-phrase literature miss is not a mathematical delta.

The package remains in progress only as a dependency for genuinely stronger conjectures.  It
must move to `not_new_scientific_knowledge` if formalized.  Neither (TS), (DF), (HF), nor (CG)
may be promoted as a discovery without an independently meaningful consequence not already
forced by the parent machinery.

## Proof architecture

1. Center \(y_i=x_i-c\) and factor
   \(K_X(t)=D_t A_t D_t\), where
   \(A_t(i,j)=e^{2t\langle y_i,y_j\rangle}\).  This proves
   \(Z_X(t)=\det A_t\).
2. Restrict to the finite span of the \(y_i\).  Expand \(A_t\) in the symmetric Fock
   feature basis indexed by multi-indices.
3. Apply finite Cauchy--Binet to truncations.  Every coefficient is a sum of squared
   evaluation minors with positive factorial weights.  Pass to the full expansion using
   absolute convergence and continuity of the finite determinant.
4. Apply finite Cauchy--Schwarz coefficientwise at scales \(a\) and \(b\), then pass to
   the limit, giving (TS).  The formal parent theorem
   `gradedPartition_mul_sq_le` is the finite engine.
5. Differentiate the absolutely convergent positive series on compact positive intervals.
   The first logarithmic derivative is the mean degree and the second is its variance.
   `gradedFirstMoment_sq_le_partition_mul_secondMoment` is the cross-multiplied finite engine.
6. The least nonzero exponent is the minimum weight of a basis of the filtered polynomial
   evaluation matroid.  Greedy rank accounting gives
   \(\nu_X=\sum_m(N-h_m(X))\).
7. Repeat the diagonal factorization about an arbitrary origin and use the Hilbert centroid
   variance identity to prove (CG).

## Hostile checks and falsifiers

- **Repeated points:** the determinant vanishes identically.  (TS) remains meaningful, but
  logarithmic formulas require distinct points or an explicit nonzero hypothesis.
- **Infinite configuration:** no infinite determinant is claimed.  Only the ambient Hilbert
  space may be infinite-dimensional; every finite configuration lies in a finite span.
- **Complex Hilbert space:** the real metric can be handled by realification, but the first
  theorem is stated over real Hilbert spaces to avoid hiding conjugation conventions.
- **Uncorrected log-convexity:** \(\det K_X(t)\) itself need not be multiplicatively log-convex
  with unit correction.  The centroid energy factor is essential and is metrically canonical.
- **Generic-only Vandermonde order:** complete monomial counts do not give the exact exponent
  on degenerate or lower-dimensional configurations; (HF) uses the actual evaluation ranks.
- **Novelty falsifier:** any source giving the centroid-corrected determinant as a positive
  graded Fock/Pluecker partition with the same elasticity-variance and cumulative-deficit
  endpoint forces reclassification as `[REDISCOVERED]` or `[BRIDGE]`.

## Lean programme

- [x] Parent layer: finite nonnegative graded partition, multiplicative midpoint law, and
  degree-variance inequality (`HilbertMetric/GradedPartition.lean`).
- [x] SOTA connector: finite rectangular Gram/Cauchy--Binet expansion into squared minors,
  exterior-power proof, and weighted Pluecker connector pass a clean targeted check in
  `HilbertMetric/GradedPartition.lean`.
- [x] Hilbert layer: ordered-tensor Fock truncations, finite-span reduction, determinant limit,
  and universal multiplicative convexity pass a clean targeted check in
  `HilbertMetric/GaussianFock.lean`.
- [x] Gaussian layer: centroid diagonal gauge, the connector from the universal Fock law to the
  centroid-corrected metric determinant, and the raw three-scale inequality pass a clean
  targeted check in `HilbertMetric/CentroidGauge.lean`.
- [ ] Algebraic endpoint: filtered evaluation ranks and cumulative-deficit identity.

## Literature audit log

- Flat-kernel determinant asymptotics and eigenvalue degree groups are established by
  Barthelme--Usevich and earlier RBF work; the generic flat-order proposal was retired.
- Non-unisolvent Gaussian flat limits and least polynomial interpolation are established
  adjacent theory; bare convergence to polynomial interpolation is not new.
- Tropical positive-definite principal minors and valuated delta-matroid formulations are
  established; the bare principal-minor valuation proposal was retired.
- Searches for `Gaussian kernel determinant bandwidth log convex`, `multiplicatively convex`,
  `degree variance`, `Hilbert function flat limit`, and `valuated matroid Gaussian kernel`
  found the parent topics but no exact degree-flow theorem.
- A second pass through entrywise PSD preservers and Oppenheim--Schur determinant inequalities
  confirmed that entrywise exponential positivity and uncorrected determinant monotonicity are
  classical; neither is claimed.  Searches for the exact positive determinant coefficients,
  centroid correction, multiplicative defect, and degree-flow phrasing found no equivalent.

## Log

- 2026-07-19 — created after retiring the poset innovation and Hilbert-cube routes, locating
  the flat-RBF determinant parents, and narrowing novelty to the centroid-corrected degree flow.
- 2026-07-19 — SOTA Lean parent layer compiled by targeted `lake env lean`; no module build run.
- 2026-07-19 — implemented an ordered-tensor (rather than multi-index) Fock truncation.  This
  makes the factorial normalization canonical in Lean, identifies every truncation with a
  weighted Pluecker partition, proves entrywise Taylor convergence and determinant convergence,
  and reduces arbitrary finite Hilbert families to their finite spans.  Verification is pending;
  no promotion claim is made before the exact source and final module gates pass.
- 2026-07-19 — all three implemented SOTA leaves passed separate `lake env lean` checks.  The
  algebraic flat-endpoint layer remains open, so the foundation card stays in progress and no
  final module build or Stage-3 claim has been made.
