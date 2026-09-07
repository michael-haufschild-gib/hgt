# EDQ second logarithmic flux with all arithmetic jumps

- **ID:** EDQ-LSF
- **Stage:** 3-formalized
- **Type:** exact arithmetic source theorem; dependency-closed paper proof and Lean audited
- **Source:** [first flux](../3-formalized/edq-logarithmic-response-height.md), [disk admission](../3-formalized/edq-reflection-disk-admission.md)

## Full chain

Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. Both present error disks admit actual nonzeros at large height. This component retains the discrete arithmetic information appearing in the next differentiation of the complete source flux.

## Exact second flux

Let `P=bernoulliPeriodic+1/12`, `Q=fract-1/2`, `l=log(x)`, and `e=exp(i*t*l)`. The first flux amplitude is

`D=Q*x^(-3/2)*l+P*x^(-5/2)*(1-3*l/2)`.

The next boundary is `A=x*D*e`. Its regular derivative away from integer jumps is `(E+i*t*D)*e`, where

`E=x^(-1/2)*l+Q*x^(-3/2)*(2-2*l)+P*x^(-5/2)*(9*l/4-3)`.

At each integer `n`, `P` is continuous and `Q` jumps down by one, so `A` jumps down by the exact logarithmic atom

`H_t(n)=n^(-1/2)*log(n)*exp(i*t*log(n))`.

For every natural `m`, `N=m+1`, unit-interval integration with the jumps retained gives

`integral_1^N E*e + i*t*integral_1^N D*e = A(N)-A(1)+sum_(k<m) H_t(k+2)`.

This will be proved by a complex finite fractional-part integration identity and right-derivative FTC for the continuous periodic quadratic. All finite-interval integrability obligations remain explicit.

## Positive survivor: compensated arithmetic limit

The actual boundary satisfies `A(1)=1/12` and tends to zero. The first flux is absolutely integrable. Therefore, with the sum and regular integral kept together,

`lim_(m→infinity) [sum_(k<m) H_t(k+2)-integral_1^(m+1) E*e] = 1/12+t^2*L_full(t)`.

This is an unconditional full-height identity, including `t=0`. No convergence of the uncompensated sum or regular integral is asserted. In particular, the second integration cannot discard the jumps and retain the same source. The limiting arithmetic expression still needs a signed comparison with the exact zero target; RH is not obtained from its existence.

The exact finite error of this compensated expression is

`-i*t*integral_N^infinity D*e-A(N)`.

Its norm is at most `abs(t)*integral_N^infinity M+norm(A(N))`, where `M` is the proved integrable first-flux majorant. This certificate preserves the height factor for moving cutoffs. The representation introduces no additional zero condition or orientation sign.

## Gates

- [x] Corpus fractional-part integration, first flux, and current ledgers inspected.
- [x] Paper derivative, integer jump, finite identity, boundary cancellation, compensated limit.
- [x] Scratch proofs and complete source identification.
- [x] Leaf wiring, targeted build, new-only axioms, lint run, both current ledgers.
- [x] Index refreshed once; all owned processes exited; three temporary Lean sources removed.
- [ ] Global lint clean: two unrelated concurrent modules are unwired.
- [ ] Signed arithmetic comparison excluding off-line zeros; RH.

## Lean inventory and final audit

Leaf: `GaloisForLFunctions.RHTower.ArithmeticLogarithmicSecondFlux`, namespace `RHTower.DeletionMixedRefinement`. 415 lines, 20 theorems and eight definitions.

- `intervalIntegrable_complex_fract_mul`, `integral_unit_complex_fract_derivative`, `integral_one_to_succ_complex_fract_derivative`: complex finite fractional-part integration, retaining every integer contribution.
- `criticalLogJumpAtom`, `criticalLogSmoothBoundary`, `criticalLogJumpDerivative`, `criticalLogSmoothDerivative`: literal jump and smooth profiles with their actual differentiated logarithmic phases.
- `criticalLogSecondBoundary`, `criticalLogSecondRegularKernel`, `criticalLogSecondRegularDensity`: complete boundary and regular second flux.
- `hasDerivAt_criticalLogJumpAtom`, `hasDerivAt_criticalLogSmoothBoundary`, `continuousOn_criticalLogSecondDerivatives`: derivatives and all positive-ray continuity requirements.
- `criticalLogSecondBoundary_eq`, `criticalLogSecondRegularDensity_eq`, `criticalLogSecondBoundary_nat`, `criticalLogSecondBoundary_one`: exact source identification and post-jump/unit values.
- `criticalLogSecondFlux_finite`: all-cutoff finite identity, every jump retained.
- `tendsto_criticalLog_power_log_zero`, `tendsto_criticalLogJumpAtom_zero`, `tendsto_criticalLogSmoothBoundary_zero`, `tendsto_criticalLogSecondBoundary_nat_zero`: complete infinite-boundary closure.
- `criticalLogSecondCurrent`, `criticalLogSecondCurrent_eq`, `criticalLogFlux_second_height_identity`, `tendsto_criticalLogSecondCurrent`: actual compensated arithmetic current, finite reconstruction, and exact full-height limit.
- `criticalLogSecondCurrent_sub_limit`, `norm_criticalLogSecondCurrent_sub_limit_le`: exact omitted tail and its literal height-dependent majorant certificate.

Foreground scratch passed without messages. `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticLogarithmicSecondFlux` compiled only the new leaf in 4.6 seconds; all dependencies were cached. The umbrella import is wired. No full or umbrella build ran.

All 28 new declarations were audited once; only `propext`, `Classical.choice`, and `Quot.sound` occur. No existing declaration was re-audited. No numerical experiment or computational certificate was used.

Formal lint reported exactly two unrelated umbrella reachability errors: `SquareRootAbelDirichletContinuation` and `SquareRootAbelDirichletKernel`. The new leaf has no lint issue. Concurrent files were left untouched; global lint is not clean. Logs: `/tmp/edq_second_flux.{check,build,axioms,lint,index}.log` and `/tmp/edq_second_flux_probe.log`.

The corpus index was refreshed once. All owned Lean processes exited, and the three scratch/probe/axiom Lean sources were removed. Logs remain available.

The new limit is an exact arithmetic representation of the full source, not an independent zero condition. No signed separation or RH proof/falsification is asserted.
