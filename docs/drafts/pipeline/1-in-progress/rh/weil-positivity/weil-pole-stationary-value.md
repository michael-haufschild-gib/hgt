# Actual stationary pole equations and the remaining value moment

Status: actual arithmetic value comparison in progress. RH remains open.

Proof chain: actual prime–Gamma pole positivity → integrated Chebyshev square-root control → bounded critical resolvent → RH.

## Closed mathematical knowledge

The complete first jets, a uniform exponential boundary/diagonal slope bound, and the resulting square-root pointwise Chebyshev estimate at stationary actual even poles are formal. The estimate applies to every interior actual even-gap minimum above radius two. The exact additional value moment is `H(a)=sum Lambda(n)(1+1/n)log n`, and actual even nonnegativity is equivalent to `H(a)≥2a[psi(exp(2a))+M1(exp(2a))]-A(a)-C_sm(a)`.

The generic claim that positivity and the two mass totals recover the value fails. Every nonnegative triple at 2,3,4 with total six and reciprocal mass two is classified, and its attainable cross-value interval is exact. This preserves the entire diagonal and cross first derivative while changing the value. The full positive survivor, paper proof and Lean audit are in [stationary error and value moment](../../../3-formalized/weil-pole-stationary-error-and-value-moment.md); the [closed shortcut](../../../5-failed/weil-pole-first-jet-value-recovery.md) is confined to auxiliary weights.

## Live conjecture → proof / fail → pivot

Priority: attack the actual unbounded arithmetic sign. The [direct sign attempts](weil-pole-direct-sign-attack.md) record where divisor renewal and the positive self-pairing arguments fail to provide it. Generic lower-bound and classification work is not the active task.

1. Derive a lower bound for the actual logarithmic moment from structure of the literal Mangoldt coefficients, using the stationary equation where applicable. Mere mass positivity is insufficient, as the complete finite model shows.
2. Test whether such a bound reaches the exact even-value threshold, retaining Gamma, pole and reciprocal errors. A larger-scale lower bound that loses the required sign must be classified by its sharp positive survivor.
3. Include boundary minima and the bounded-radius range. The stationary error theorem only covers interior stationary points at radius at least two.
4. A successful even comparison must be combined with the genuine odd prime-power checkpoint signs in the fixed-pole RH criterion.

## Work and audit

- [x] Exact first jets and actual stationarity equation.
- [x] Boundary/diagonal slope bounds and stationary Chebyshev estimate.
- [x] Weighted-log value moment, complete finite model and sharp attainable range.
- [x] Foreground scratch checks and three named leaf builds; umbrella imports wired.
- [x] All 34 public declarations have exactly the standard three axioms; formal lint and whitespace checks passed.
- [x] Current frontier and universal knowledge updated.
