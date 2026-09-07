# EDQ horizontal comparison of the actual incoming aggregate

- **ID:** EDQ-IHC
- **Stage:** 3-formalized
- **Type:** THEOREM; paper and Lean audited
- **Source:** [current frontier](../1-in-progress/rh-current-frontier-map.md), [outgoing margin](edq-outgoing-uniform-margin.md)

## Full chain

Euler deletion → exact arithmetic remainder → off-line-specific cumulative incoming comparison → off-line-zero exclusion → RH. The outgoing error is controlled at high height; the remaining comparison must preserve the actual positive critical incoming contribution. This component controls the change of the full source with horizontal displacement, uniformly in the moving cutoff.

## Source calculation

At unit anchor, the k-th incoming term integrates over `1<x<=t/(2*pi*k)`. Its phase `-2*pi*k*x+t*log(x)` and endpoint depend only on height. Changing `sigma` to `tau` changes only its real power amplitude. The exact complex difference is the integral of

`w_(-k)*(x^(-sigma-2)-x^(-tau-2))*exp(i*(-2*pi*k*x+t*log(x)))`.

For `x>=1`, `sigma,tau>=0`, the exponential tangent inequality gives

`abs(x^(-sigma-2)-x^(-tau-2)) <= abs(sigma-tau)*x^(-2)*log(x)`.

The full logarithmic moment from one to infinity equals one. The finite positive-frequency coefficient mass is at most `1/24`. Therefore the actual complex aggregate, at the same height and same arbitrary frequency cutoff K, satisfies

`norm(H(s,1,K)-H(z,1,K)) <= abs(Re(s)-Re(z))/24`.

This is an estimate for the actual sum, uniform in height and cutoff. In particular, comparing `s` and `1-conj(s)` produces error proportional to `abs(2*Re(s)-1)`, with exact zero error on the critical line. This is magnitude control; the signed horizontal difference still needs arithmetic orientation.

## Positive source neighborhood

The outgoing-margin theorem supplies actual critical zeros above every height with `Im(H)>1/(240*t)`. At the same height, every horizontal shift of size at most `1/(20*t)` with nonnegative real part then has `Im(H)>1/(480*t)`. In particular, the explicit strict-right point with real part `1/2+1/(40*t)` has positive incoming aggregate. The new point is not asserted to be a zeta zero or a nonzero of zeta.

This gives cofinally high actual strict-right source points with positive head; blanket eventual head nonpositivity even on the strict-right strip cannot be the selector. The positive survivor is a uniform displacement estimate and explicit positive neighborhood. Comparisons conditioned on off-line zeros or relative to their exact boundary data remain open.

## Lean inventory and final audit

Leaf: `GaloisForLFunctions.RHTower.ArithmeticIncomingHorizontalComparison`, namespace `RHTower.DeletionMixedRefinement`. 248 lines, 14 new theorems, no new definitions.

- `incoming_power_difference_le_of_le`, `incoming_power_difference_le`: symbolic exponential tangent bounds.
- `bernoulliFourierTerm_horizontal_difference`, `norm_bernoulliFourierTerm_horizontal_difference_le`, `stationaryIncomingAtom_horizontal_difference`, `norm_stationaryIncomingAtom_horizontal_le`: literal finite integral and common logarithmic majorant.
- `sum_negativeBernoulliWeight_le`, `norm_stationaryIncomingSection_horizontal_le`, `stationaryIncomingSection_horizontal_difference`, `stationaryIncomingSection_im_horizontal_le`: full coefficient mass and actual aggregate comparison.
- `norm_stationaryIncomingSection_reflection_difference_le`: reflection error proportional to horizontal displacement.
- `stationaryIncomingSection_positive_horizontal_neighborhood`, `stationaryIncomingSection_positive_near_critical_zero`, `exists_strict_right_stationaryIncoming_positive_above`: positive source neighborhood and cofinal strict-right witness.

Foreground scratch passed; the sole unused-parameter warning was removed before final audit. `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticIncomingHorizontalComparison` built only the new leaf in 6.1 seconds, reusing cached dependencies. The umbrella import is wired; no umbrella or full build ran. All 14 new theorems were audited once, with only `propext`, `Classical.choice`, and `Quot.sound`; no existing declaration was re-audited. Formal lint passed with existing size warnings only. No numerical experiment or computational certificate was used. Logs: `/tmp/edq_horizontal_{build,axioms,lint}.log`.

The positive strict-right source witness does not falsify RH: it asserts neither vanishing nor nonvanishing of zeta at that point. The remaining requirement is a signed comparison using the actual off-line-zero constraints or other exact relative data. The Lipschitz bound supplies magnitude control and exact critical cancellation, not that missing sign.

## Gates

- [x] Corpus search and exact source inspection.
- [x] Foreground scratch check: exact difference, power bound, finite mass, aggregate comparison.
- [x] Positive neighborhood and cofinal strict-right source witness.
- [x] Leaf wiring, targeted final audit, new-only axioms, formal lint.
- [x] Both ledgers and corpus index refreshed. Three temporary Lean sources removed; all owned Lean processes exited.
- [ ] Signed off-line-specific comparison and unconditional RH proof/falsification.
