# Finite Weil uniform exponential control and all scalar moments

Status: dependency-closed paper proof and exact Lean formalisation complete.

## Exact claim

Let `X_r` have the actual projected index law with coefficients `(1,0)`, centered at its actual mean and divided by `sqrt(r+1)`, at `k = 2(r+1)^2+t(r)`. For every offset family:

- `E exp(a X_r) ≤ 4 exp(|a| + a^2/8)` for every real `a` and every rank.
- `E exp(|X_r|) ≤ 8 exp(9/8)`.
- `E |X_r|^p ≤ p! * 8 exp(9/8)` for every natural `p`.
- Every integer moment `E X_r^p` tends to the corresponding moment of the actual projected Gaussian `(1,0)`, whose variance is `1/4`.

All final finite Weil statements have only natural parameters and real test parameters, with no unproved analytic premises.

## Dependency-closed proof

The canonical mass profile differs from the arithmetic profile by at most the arithmetic profile times `|i-center|/(r+1)`. That ratio is at most one. Thus the numerator is at most twice the arithmetic numerator; the existing normalization lower bound is half the arithmetic mass. The actual midpoint probability is therefore at most four times the binomial probability, pointwise.

The local binomial Hoeffding theorem gives the centered exponential bound `exp(n*a^2/8)` for `n` trials. Substituting `a/sqrt(r+1)` with `n=r+1` gives `exp(a^2/8)`. Jensen's two-point inequality for the exponential, combined with the exact endpoint-pairing identity, bounds the arithmetic-centered edge exponential by the midpoint exponential. Its bound is therefore `4 exp(a^2/8)`.

The actual edge mean differs from `r/2` by at most `sqrt((r+2)/2) ≤ sqrt(r+1)`. Recentring thus costs at most `exp(|a|)`, proving the first bound. The two signs `a=1,-1` and `exp(|x|) ≤ exp(x)+exp(-x)` give the second. The corpus's inequality `|x|^p ≤ p! exp(|x|)` gives the third.

The actual laws already converge weakly to the projected Gaussian. For each natural moment order, the new uniform bound at twice that order supplies the tail hypothesis of `HTGeometry.tendsto_integral_pow_of_uniform_even_moment`. Finite atomic source laws integrate every real test; Gaussian powers are integrable by the existing Gaussian `MemLp` theorem. Bounded truncations are integrable under both probability measures. Hence the receiver's hypotheses are all discharged, including order zero separately.

## Lean scope

- `RHTower.WeilLogShiftBinomialExponential`
- `RHTower.WeilLogShiftMidpointDomination`
- `RHTower.WeilLogShiftEdgeExponential`
- `RHTower.WeilLogShiftProjectedMomentBounds`
- `RHTower.WeilLogShiftProjectedMomentLimit`

Only local Lean corpus used as mathematical sources. No numerical evidence, external literature or additional axioms.

## Relation to broader work

This closes the scalar tail-control and moment-limit stage of `finite-weil-joint-quantile-all-moments`. Common-uniform joint convergence in every finite moment remains in progress on that card; this result does not itself claim it.

## Verification

- Five targeted native leaf builds: terminal exit 0, empty logs. No umbrella or full build.
- Fourteen public theorems; all fourteen final `#print axioms` audits use only `propext`, `Classical.choice`, `Quot.sound`. Thirty-four supporting API names verified in the final native scratch audit.
- Eleven direct imports and nine incoming imports checked. Each new leaf appears once in its theorem-area umbrella. Declaration uniqueness, source/object freshness and direct dependency freshness checks passed.
- Local research index returns all six moment-bound/limit declarations with no markers. The prior scoped search returned 47 hits; all three result pages were inspected.
- Global `scripts/formal_tools.py lint`: ten unrelated errors, 367 warnings, no finding in these five leaves. Unreachable modules: `CCMPolarOddPrimeJumps`, `WeilRationalCuspLockRigidity`, `WeilRationalCuspLockSpectrum`, `XiCriticalityLocalRigidity`, `XiCriticalityResonanceDensity`, `XiGaussianHeatHankelLargeTimeInertia`, `ZetaCriticalNonRigidDensity`, `HTGeometry.HermiteGaussianMomentBounds`, `HTGeometry.QKrawtchoukCompanionTriangular`. Existing proof debt: `CCMPolarOddPrimeJumps.lean:104`, `ccmPolarOddSource_eq_core_add_atoms`.
- Scoped `git diff --check` passed. Audit artifacts: `/tmp/hgt-all-moments-{metadata.json,declarations.json,incoming-imports.txt,final-audit.lean,final-audit.log,roots-search.json,lint.log}`.
