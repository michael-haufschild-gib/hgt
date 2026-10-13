# Finite Weil polynomial covariance rank

Status: formalized; ten new theorems and one matrix definition across five leaves, native and axiom audits passed (2026-10-12).

## Objective and local evidence

For each fixed n, prove positive definiteness of the Gaussian covariance matrix
of x,x^2,...,x^n and eventual positivity of the corresponding actual finite Weil
covariance determinant. This supplies arbitrarily many independent polynomial
covariance directions as degree increases.

Only local Lean evidence is used. The polynomial covariance/positive query had
one unrelated mass-scaling hit. The scoped Weil covariance/determinant query had
no hits; the broader covariance query recovered 13 declarations with full
coverage. Existing polynomial covariance convergence supplies each matrix entry.
GaussianContinuousVarianceRigidity supplies pointwise constancy from zero
variance. Existing Gaussian monomial integrability discharges every L2 premise.
The corpus also has strict Gaussian-window Hankel positivity, for uncentered
weighted moments; this increment concerns centered probability covariance and
actual finite Weil limits. Installed covariance finite-sum identities and
positive-definite determinant positivity complete the proof route.

## Dependency-closed paper proof

1. If sum_i c_i*x^(i+1) vanishes for every real x, the corresponding polynomial
   is zero by extensionality over the infinite real field. Its coefficient at
   i+1 equals c_i, so every c_i is zero.
2. Gaussian monomials lie in L2 because their squares are monomials and all
   Gaussian monomials are integrable. Finite sums remain L2. Zero variance of
   the continuous power sum makes it constant everywhere; its value at zero is
   zero, so step 1 forces the coefficient vector to vanish. Conversely the zero
   vector has zero variance.
3. For a square-integrable family, the covariance matrix quadratic form equals
   the variance of the corresponding linear combination. This follows from
   covariance_self and the finite-sum/scalar covariance identities. Symmetry
   supplies Hermitian symmetry over the reals.
4. For Gaussian powers, every nonzero coefficient vector therefore has strictly
   positive quadratic form. The matrix is positive definite, hence its
   determinant is positive, for every fixed size n, including n=0.
5. Existing actual polynomial covariance convergence, applied to powers of the
   first coordinate, gives entrywise matrix convergence. The determinant is
   continuous, so actual determinants converge to the strictly positive Gaussian
   determinant and are eventually positive.

## Plan and working log

1. Audit current APIs; prove real power-sum rigidity and Gaussian variance rigidity.
2. Define the power covariance matrix; prove its quadratic-form identity and the
   Gaussian positive-definite/determinant results.
3. Prove actual matrix and determinant convergence, then eventual positivity.
4. Sequential native builds, umbrella wiring, complete declaration/axiom/index
   audits, whitespace, and one final lint snapshot.

- All 22 installed API references passed natively with an empty log.
- RealPowerSumRigidity passed natively with an empty log, including size zero.
- All five leaves are written. The generic power covariance matrix definition is
  included in the final declaration and axiom audit, alongside the ten theorems.
- All 13 scoped covariance hits were reviewed using existing source evidence and
  the remaining statement headers. They cover pairwise/coordinate covariance,
  residual identities, and existing observable limits, not this determinant root.
- GaussianPowerVariance passed with an empty native log.
- PowerCovarianceMatrix passed with an empty native log. Its first build exposed
  an import and notation boundary: covariance_self and variance are defined in
  Mathlib.Probability.Moments.Variance; covariance_comm takes both observable
  arguments explicitly; `.mulVec` avoids the scoped multiplication notation.
  These were corrected without changing the theorem statements mathematically.
- GaussianPowerCovariance passed with an empty native log. Its quadratic-form
  rewrite needs an explicit `id` function argument; leaving it implicit inferred
  an extensionally equal lambda that the rewrite matcher did not unfold.
- WeilLogShiftPowerCovarianceLimit passed with an empty native log: actual matrix
  convergence, determinant convergence, and eventual determinant positivity.
- Final audit imported the actual root using
  `lake --old env lean /tmp/hgt-weil-polynomial-gram-final-audit.lean`.
  All eleven declarations use only propext, Classical.choice, and Quot.sound;
  all 22 API references passed with no residual diagnostics.
- Metadata audit verified five fresh native objects and empty logs, seven direct
  project import edges (fifteen imports including Mathlib), nine incoming imports,
  fresh direct project dependencies, unique declarations including the
  noncomputable matrix definition, and one umbrella import per new leaf.
  New Lean files and both umbrellas passed whitespace checks. No umbrella or
  full build was run.
- Scoped local index audit recovered all eleven declarations with full coverage,
  no partial results or markers, and empty stderr.
- Final repository lint snapshot: five errors outside this increment and 367
  large-file warnings. Unreachable modules: JointAncestryRealAmplitudeDetection,
  PaperHurwitzCompactObservation, PaperWoldCompositeNormContinuity,
  PaperWoldCompositeNormValues, and PaperWoldCompositeObservation. No error
  concerns this increment. Global lint is not claimed clean.
- Audit artifacts use the prefix `/tmp/hgt-weil-polynomial-gram`.

## Formalized declarations

- HTGeometry/RealPowerSumRigidity: real_power_sum_succ_eq_zero_iff.
- HTGeometry/GaussianPowerVariance: gaussianZero_memLp_two_nat_pow,
  gaussianZero_variance_power_sum_zero_iff.
- HTGeometry/PowerCovarianceMatrix: powerCovarianceMatrix (definition),
  powerCovarianceMatrix_isHermitian, powerCovarianceMatrix_quadraticForm.
- HTGeometry/GaussianPowerCovariance: gaussianZero_powerCovarianceMatrix_posDef,
  gaussianZero_powerCovarianceMatrix_det_pos.
- RHTower/WeilLogShiftPowerCovarianceLimit:
  tendsto_finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix,
  tendsto_finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det,
  eventually_finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_pos.

## Boundary

Each polynomial degree n is fixed before taking the limit. No threshold uniform
in n, explicit growth rate, finite-depth full polynomial rank, or bounded-degree
quotient dimension formula is asserted. Actual-law roots retain canonical depths
2*(r+1)^2+t(r) and subcritical base tilts. The corpus-wide goal remains active.

Next candidate, not proved here: use the exact finite-support variance criterion
to relate finite power-covariance rank directly to the number of distinct
first-coordinate support values. This may remove the asymptotic and subcritical
restrictions from the positivity statement; the support cardinality and exact
degree threshold still require source inspection and proof.
