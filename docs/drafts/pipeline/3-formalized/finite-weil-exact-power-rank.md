# Exact finite power covariance rank and nullspace

Status: formalized and audited (2026-10-12); repository lint has five unrelated errors.

## Formal result and verification

For every `r k : ℕ`, every `a b d : ℝ`, and every power count `n`, the actual
first-coordinate power covariance matrix has rank `min n r` and kernel
dimension `n - r`. Its entire kernel equals the kernel of the finite-node
power difference matrix and is independent of all real tilt coefficients at
fixed `r k`. No asymptotic schedule, subcriticality, or positivity premise is
left at the actual-law roots.

Six theorems and one definition are formalized in three leaves:

- `HTGeometry/FinitePowerDifferenceMatrix.lean`: the difference matrix and its exact constant-node-sum kernel criterion.
- `RHTower/WeilLogShiftPowerCovarianceKernel.lean`: null-vector criterion, kernel identity, and tilt invariance.
- `RHTower/WeilLogShiftPowerCovarianceRank.lean`: exact rank and nullity.

All three native leaf builds have empty diagnostic logs and fresh objects.
The final native scratch audit imports the actual rank root, checks 13 APIs
and two concrete API examples, and reports all seven declarations with only
`propext`, `Classical.choice`, and `Quot.sound`. There are no residual
diagnostics. Full index coverage is 7/7 (2 + 3 + 2). Declaration uniqueness,
all 5 direct project dependency edges, 8 total imports, 5 incoming imports,
umbrella wiring, and whitespace passed. Artifacts use prefix
`/tmp/hgt-weil-exact-power-rank-`.

The final `scripts/formal_tools.py lint` snapshot has 367 warnings and five
unrelated unreachable modules: `RHTower.JointAncestryRealAmplitudeDetection`,
`RHTower.PaperHurwitzMovingObservation`, `RHTower.PaperHurwitzObservationProfile`,
`RHTower.PaperHurwitzObservationScale`, and `RHTower.XiSliceHeatThresholdBelowNewman`.
No new leaf has a lint error. No web searches, external papers, or numerical
experiments were used.

## Objective and local evidence

Strengthen the finite threshold theorem to the exact rank `min n r`, kernel
dimension `n - r`, and tilt-independent kernel for the actual finite Weil law.
The previous increment proves positive definiteness iff `n ≤ r`, but does not
identify rank once the determinant vanishes. All finite `r k`, all real tilt
coefficients, and all power counts `n` remain in scope, including zero cases.

Only local Lean evidence is used. Exhaustive source search for
`powerCovarianceMatrix` found the existing definition, Gaussian positivity,
finite threshold, constant-sum null-vector lemma, and convergence results;
none state the exact finite rank. Scoped indexed search for `rank` in
`WeilLogShift` returned six fully covered declarations. All six statements
were checked: these concern joint two-coordinate fluctuation limits and
reverse Cauchy inequalities, not the power covariance matrix. A broad
covariance search was exploratory, not an exhaustive novelty audit.

Relevant existing corpus inputs are `PowerCovarianceKernel`,
`WeilLogShiftTiltVarianceKernel`, and `WeilLogShiftFinitePowerCovariance`.
Installed Lean rank APIs supply rank-nullity, principal-submatrix rank
monotonicity, and rank of an invertible matrix.

## Dependency-closed paper proof

For nodes `x : Fin (r+1) → ℝ`, let the `r × n` difference matrix have entry
`x(i+1)^(j+1) - x(0)^(j+1)`. Its null vectors are exactly power sums constant
on every node. This equivalence needs neither injectivity nor positivity.

For the actual finite tilted law, covariance null vectors have zero quadratic
form, hence zero variance, hence constant values on the whole finite support.
Conversely, constant node values give an almost-everywhere constant power sum
and therefore a covariance null vector. Thus its kernel equals the difference
matrix kernel. Rank-nullity gives equal ranks; the difference matrix has `r`
rows, so covariance rank is at most `r`, and its size also bounds rank by `n`.

Put `m = min n r`. The first `m` powers give a principal submatrix equal to the
existing positive definite size-`m` covariance matrix. Its rank is `m`.
Submatrix rank monotonicity gives the opposite bound, proving rank `min n r`.
Rank-nullity then gives kernel dimension `n - r`. The difference matrix does
not depend on tilt coefficients, so the entire kernel is invariant under
arbitrary real quadratic tilts at fixed `r k`. The exact rank also does not
depend on depth.

## Plan and working log

1. Check native APIs and the principal-submatrix definitional identity.
2. Formalize the finite-node difference matrix and its exact kernel criterion.
3. Prove the actual-law kernel identity, exact rank, nullity, and invariance.
4. Build leaves sequentially, wire umbrellas, audit every declaration and its
   axioms, check full index coverage and whitespace, then run one lint snapshot.

## Boundary

This does not assert equality of kernels across different depths, since
centering moves the nodes. It gives no determinant factorization or lower
eigenvalue estimate. Existing Gaussian limits retain their own assumptions.
