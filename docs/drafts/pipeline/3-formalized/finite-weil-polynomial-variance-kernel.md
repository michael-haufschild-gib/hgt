# Finite Weil polynomial variance kernel

Status: formalized; nine new theorems across five leaves, native and axiom audits passed (2026-10-12).

## Objective and corpus evidence

Extend the quadratic limiting kernel to every fixed real bivariate polynomial. Prove
actual polynomial moment, covariance, and variance convergence, then classify
the zero-variance limit by constancy of the diagonal restriction P(x,x).

Evidence is exclusively local Lean source. WeilLogShiftQuadraticTiltMoments
already proves every mixed monomial limit. QuadraticExponentialMoments proves
all centered Gaussian monomials integrable. VarianceGaugeRigidity identifies
zero variance of an L2 observable with almost-everywhere constancy. Installed
Mathlib supplies Gaussian absolute continuity in both directions at nonzero
variance, equality of continuous functions from volume-almost-everywhere
equality, and multivariate polynomial induction/evaluation.

The first polynomial/variance/Gaussian query had two unrelated hits.
The broad Weil covariance/diagonal query is exploratory (113 eligible entries,
first 20 inspected), not an exhaustive novelty audit. Targeted polynomial
search returned 17 entries with full coverage and empty stderr. All 17 statement
headers were inspected: weights, cluster mass limits, and Gram costs, with no
polynomial observable moment or variance-kernel theorem. Final exact declaration
uniqueness checks will cover all new names.

## Dependency-closed paper proof

1. A bivariate monomial with exponent function e evaluates to
   c*z0^(e0)*z1^(e1). On the diagonal this is c*x^(e0+e1). Finite polynomial
   induction and existing Gaussian monomial integrability give integrability
   of every diagonal polynomial. Apply this to P^2 to obtain L2.
2. The existing mixed-moment theorem gives convergence for each monomial.
   Polynomial induction adds these limits, using finite-law integrability
   and the diagonal Gaussian integrability from step 1. Thus E[P] converges
   to E[P(X,X)] for every bivariate polynomial P, at canonical depths and
   subcritical tilts.
3. Apply step 2 to P*Q, P, and Q. The covariance subtraction identity gives
   covariance convergence. Its self-case gives variance convergence. Every
   L2 premise is discharged by finite support or step 1.
4. The limiting Gaussian variance is zero iff the diagonal polynomial is
   almost everywhere constant. Nonzero Gaussian variance gives volume
   absolutely continuous with respect to that Gaussian, so constancy holds
   volume-almost everywhere. Continuity upgrades it to every real x.
   Evaluating at zero anchors the constant as P(0,0). The converse follows
   from pointwise constancy. Subcriticality ensures strictly positive Gaussian
   variance; no additional analytic assumption remains in the actual root.
5. Uniqueness of limits gives: actual polynomial variance tends to zero iff
   P(x,x)=P(0,0) for every x. The criterion contains neither tilt parameters
   nor the canonical schedule, hence the limiting kernel is universal across
   all such choices.

## Plan and working log

1. Audit installed APIs; prove Gaussian diagonal polynomial integrability/L2
   and continuous Gaussian variance rigidity in small helper leaves.
2. Prove actual polynomial moment transfer, covariance, and variance limits.
3. Prove the exact zero-limit criterion and its tilt/schedule invariance.
4. Sequential native leaf builds, umbrella wiring, complete new declaration
   axiom/import/index audits, whitespace checks, and one final lint snapshot.

No native process owned by this increment was running when work began.

- Sixteen installed API references passed natively with an empty log after
  specializing universe levels in the scratch checks.
- BinaryPolynomialGaussianMoments passed natively with an empty log. Expected
  type-directed addition and an explicit polynomial-power function equality
  avoid incidental norm-instance inference differences in `simpa using`.
- GaussianContinuousVarianceRigidity passed natively with an empty log.
- Actual polynomial moment, covariance, variance, exact kernel, and tilt/schedule
  invariance passed natively with empty logs.
- Local index queries recovered all nine new declarations, with full scoped
  coverage, no partial results or markers, and empty stderr. Final reconciliation
  against the audited source declaration list passed: nine of nine declarations.
- Final audit imported WeilLogShiftPolynomialVarianceKernel with
  `lake --old env lean /tmp/hgt-weil-polynomial-kernel-final-audit.lean`.
  All nine axiom reports contain only propext, Classical.choice, and Quot.sound;
  sixteen API checks passed with no residual diagnostics.
- Metadata audit verified five fresh native objects and empty logs, eight direct
  project import edges (twelve imports including Mathlib), nine incoming imports,
  unique declaration names, fresh direct project dependencies, and one umbrella
  import per new leaf. New leaves and both umbrella changes passed whitespace
  checks. No umbrella or full build was run.
- Final repository lint passed: zero errors, 367 existing large-file warnings.
  Audit scripts and output use the prefix `/tmp/hgt-weil-polynomial-kernel`.

## Formalized declarations

- HTGeometry/BinaryPolynomialGaussianMoments:
  binaryPolynomial_eval_monomial,
  gaussianZero_integrable_binaryPolynomial_diagonal,
  gaussianZero_memLp_two_binaryPolynomial_diagonal.
- HTGeometry/GaussianContinuousVarianceRigidity:
  gaussianReal_variance_eq_zero_iff_constant.
- RHTower/WeilLogShiftPolynomialTiltMoments:
  tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_moment.
- RHTower/WeilLogShiftPolynomialCovarianceLimit:
  tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_covariance,
  tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance.
- RHTower/WeilLogShiftPolynomialVarianceKernel:
  tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff,
  tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff_probe.

## Boundary

The kernel is a limiting kernel for fixed polynomial observables. No finite-depth
kernel equality, growing-degree uniformity, or convergence rate is asserted.
The subsequent finite-weil-polynomial-diagonal-ideal increment proves the exact
divisibility reformulation: P-P(0,0) is divisible by X0-X1. It also proves the
quotient unique and gives a unique diagonal remainder decomposition for every
real bivariate polynomial. The corpus-wide goal stays active.
