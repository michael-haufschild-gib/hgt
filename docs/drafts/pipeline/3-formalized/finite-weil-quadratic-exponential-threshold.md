# Finite Weil quadratic exponential threshold

Status: fully proved and formalized from the local Lean corpus. All seven leaves and the final native axiom audit pass; global formal lint still reports eight errors outside this increment.

## Target

For the actual projected index law at `2*(r+1)^2+t r`, prove convergence of every linear exponential moment to `exp(a^2/8)`. Then establish the exact quadratic threshold: the moments of `exp(c*x^2)` converge to the Gaussian value `sqrt(2/(2-c))` when `c<2`, and tend to positive infinity when `2<=c`, for every offset sequence `t : Nat -> Nat`. Seek one unconditional extended-real limit statement covering all real `c`, plus the sharp boundedness classification.

## Local evidence

`WeilLogShiftProjectedMomentBounds` supplies the unconditional all-parameter bound `integral(exp(a*x)) <= 4*exp(abs(a)+a^2/8)`. `WeilLogShiftProjectedMomentLimit` supplies scalar weak convergence and every integer moment limit. `WeilLogShiftQuantileMoments` supplies almost-everywhere quantile convergence and exact pushforwards. Installed Lean supplies Gaussian MGF identities, Gaussian densities, integrability of decaying quadratic exponentials, and Fatou/DCT. Local lexical `exponential moment convergence` scoped to `WeilLogShift` returns no hits. All mathematical source reads are local Lean.

## Proof mechanism and obligations

1. Transfer weak convergence through a continuous real observable. Apply the existing scalar moment-convergence theorem at order one to the pushed-forward laws. A uniform second-moment bound then gives convergence of its expectation; discharge the target bound by taking a maximum and discharge all bounded truncation integrability from probability measures.
2. Apply step 1 to `exp(a*x)`. Its square is `exp((2*a)*x)`, so the existing all-parameter bound supplies the missing uniform second moment. Gaussian exponential integrability and its explicit MGF discharge the target ingredients.
3. For nonnegative `c`, express `exp(c*x^2)` as the standard Gaussian average of `exp(sqrt(2*c)*z*x)`. Since the source is finite atomic, exchange this average with its finite expectation. Linear MGF convergence becomes pointwise convergence in `z`.
4. The existing MGF bound gives the Gaussian-average envelope `4*exp(sqrt(2*c)*abs(z)+c*z^2/4)`. Its product with the standard Gaussian density is integrable exactly below `c=2`; prove integrability by absorbing the linear term into a smaller decaying quadratic or by completing the square. DCT yields subcritical quadratic convergence. For nonpositive `c`, use direct bounded DCT on common quantiles.
5. Evaluate the limiting quadratic Gaussian integral and prove its integrability threshold using the actual variance `1/4` and the local Gaussian integral theorem.
6. At and above criticality, use Fatou on the nonnegative common-quantile observables: limiting extended integral is top, hence actual finite moments tend to positive infinity. Convert to an unconditional extended-real statement and derive boundedness iff `c<2`.

The threshold conclusion remains open until every obligation above is verified. Linear exponential convergence alone does not close this card.

## Verification

Native leaf builds only, one owned build at a time, empty-log gates, exact umbrella imports, final native scratch axiom audit, scoped freshness/import checks, and authoritative global formal lint. No computations, external reading, heartbeat increases, full builds, or commits.

## Formal result

For every `t : Nat → Nat`, let `X_r` have the actual projected index probability law at `k_r = 2*(r+1)^2 + t r`. Every real linear exponential moment tends to `exp(theta^2/8)`. The quadratic moments `E exp(c*X_r^2)` tend to `sqrt(2/(2-c))` for `c < 2`, and diverge to positive infinity for `2 ≤ c`. Their range is bounded above exactly when `c < 2`. An unconditional extended-integral theorem combines both branches for every real `c`. These final roots have no analytic assumptions; parameter subtypes express the sharp ranges of `c`.

The positive survivor at the obstruction is the exact boundedness classification and complete subcritical limit, including arbitrary nonnegative depth slack `t`. The Gaussian Bochner integral formula alone returns zero outside integrability; the criticality theorem instead proves divergence of the actual finite expectations, and the extended integral records infinity.

## Native closure

Seven leaves compile with terminal exit zero and empty logs: `HTGeometry.WeakContinuousMomentTransfer` (1 theorem), `HTGeometry.GaussianQuadraticExponential` (6), `HTGeometry.IntegralFatouDivergence` (1), `RHTower.WeilLogShiftProjectedExponentialLimit` (3), `RHTower.WeilLogShiftGaussianAveraging` (3), `RHTower.WeilLogShiftQuadraticExponentialLimit` (8), and `RHTower.WeilLogShiftQuadraticExponentialCriticality` (3). Each is imported once by its theorem-area umbrella; no umbrella build was run.

Final native audit `lake --old env lean /tmp/hgt-weil-quadratic-exponential-final-audit.lean` exits zero. All 25 declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; 44 local mathlib API probes pass, with no residual warnings or unexpected output. Metadata checks report no issues across seven leaves, 15 direct import edges, and 13 incoming imports. Refreshed lexical corpus search returns all 11 declarations in the two quadratic-exponential leaves, with no coverage markers. Scoped `git diff --check` passes.

Authoritative global lint exits one with eight unrelated errors: unreachable `RHTower.CCMPolarOddPrimeJumps`, `RHTower.PaperLiNegativeCutoffs`, `RHTower.PaperLiNegativeOperator`, `RHTower.PaperLiNegativeProfile`, `RHTower.PaperLiNegativeSuppression`, `RHTower.XiSliceOffCentreArcTail`, and `HTGeometry.QKrawtchoukCompanionTriangular`, plus a `sorry` in `RHTower.CCMPolarOddPrimeJumps.lean:104`. None names a leaf in this increment. Those files remain outside this task's write scope.

Artifacts: `/tmp/hgt-weil-quadratic-exponential-{metadata.json,incoming-imports.txt,final-audit.lean,final-audit.log,audit-summary.json,lint.log,index.json}` and `/tmp/hgt-<Leaf>.log`. API details: rewrite pushed-forward power integrals before simplifying `pow_one`; Gaussian wrapper integrability needs `simpa [finiteWeilProjectedGaussian]`; prove nonzero `NNReal` variance by applying coercion to a hypothetical equality; use `tendsto_of_le_liminf_of_limsup_le` for the Fatou step, since `Filter.liminf_eq_top` requires a countable-intersection filter unavailable for `Nat.atTop`.
