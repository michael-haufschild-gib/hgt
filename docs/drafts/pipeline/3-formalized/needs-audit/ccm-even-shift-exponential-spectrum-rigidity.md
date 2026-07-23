# CCM even-shift exponential-spectrum rigidity

- **ID:** `ccm-even-shift-exponential-spectrum-rigidity`
- **Stage:** 3-formalized/needs-audit
- **Type:** UNIVERSAL THEOREM / CCM FIXED-SHIFT NO-GO
- **Scientific status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [NOVELTY-AUDIT-OPEN]
  [NOT RH] [NOT WHOLE-CCM DEATH]`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/CCMPublishedSourceEvenShiftSieve.lean`
  - `formal/GaloisForLFunctions/RHTower/CCMEvenShiftExponentialTypeRigidity.lean`

## The universal law

For an eventually nonnegative aperture carrier `eta`, suppose a scalar source multiplier `w`
is eventually bounded and bounded away from zero:

```text
0<c<=w(h)<=C<infinity.
```

For every real exponent `epsilon`, Lean proves the exact rate-spectrum equivalence

```text
eta(h) <= O(exp(epsilon*h))
  iff
w(h)eta(h) <= O(exp(epsilon*h)).
```

Consequently `eta` has zero exponential type iff `w eta` has zero exponential type. The theorem
also applies whenever `w(h)` tends to a positive constant.

The result extends from one multiplier to the complete finite fixed-shift algebra. A polynomial
`P` in the shift has physical multiplier `|P(exp(-q h))|`. Lean proves:

```text
P(0) != 0  =>  every exponential upper-rate budget is unchanged;
an upper-rate improvement  =>  P(0)=0;
P=X^m Q, Q(0)!=0  =>  every rate is translated by exactly q*m.
```

Thus shift-polynomial units are rate-inert, while exponent-changing elements lie in the
augmentation ideal and are asymptotically noninvertible. This is a classification, not only a
shift-two counterexample. More intrinsically, for every nonzero `P`, Lean factors at zero and
proves that `rootMultiplicity(0,P)` alone is the exact rate translation; all remaining
coefficients are rate-invisible.

## Actual published CCM source

The physical-space coboundary of spectral translation by `q>0` is

```text
w_q(h)=1-exp(-q h).
```

It satisfies `1/2<=w_q(h)<=1` eventually. For the published shift `q=2`, Lean proves the local
Gamma cancellation

```text
(1-exp(-2h))*rho_infinity(h)=exp(-h/2),  h>0,
```

and the complete rate-by-rate tail law

```text
|(1-exp(-2h))*E_crit(h)| <= O(exp(epsilon*h))
  iff
|E_crit(h)| <= O(exp(epsilon*h)).
```

Thus a fixed even shift solves the local Gamma singularity but is exactly inert at the
infinite-aperture exponent which the corpus identifies with the Xi transverse divisor frontier.
It cannot supply the missing half-unit continuation or prove zero exponential type.

## Finite-aperture separation law

At every positive aperture and nonzero physical clock mode, the same Lean development proves:

1. the filtered Gamma coefficient is the explicit strictly positive term

```text
(1/pi) * xi*(1-exp(-kappa*2a))/(kappa^2+xi^2);
```

2. the remaining polar--prime term is exactly one completed-error derivative moment;
3. the complete filtered source is negative iff that arithmetic moment crosses the negative of
   the displayed Gamma budget.

No RH premise, zero location, estimate, numerical computation, finite-rank restriction, or
simple-evenness premise occurs.

## Frontier consequence

This kills the complete class of fixed-shift scalar regularizations as an RH-closing mechanism.
A surviving CCM transport must be asymptotically singular/noninvertible at the aperture boundary,
or must be genuinely operator-valued and orbit-sensitive before scalarization. That is consistent
with the corpus's independent dense-nonclosed-range and basiswise Pick-rigidity theorems.

It does not kill the whole CCM lane. The exact open endpoint remains source-normalized Evans
nonvanishing, equivalently the four-unit Xi graph relative-trace contraction / zero exponential
type of the completed critical-Mellin error.

## Formal declarations

- `ccmPublishedEvenShiftSievedTest_eq_shiftDifference`
- `one_sub_exp_neg_two_mul_ccmPublishedArchimedeanDensity`
- `ccmPublishedEvenShiftSievedArchCoefficient_physical_eq`
- `ccmPublishedEvenShiftSievedArchCoefficient_physical_pos`
- `ccmPublishedEvenShiftSievedSourceCoefficient_physical_closed`
- `ccmPublishedEvenShiftSievedSourceCoefficient_physical_neg_iff`
- `apertureExponentialUpperBound_mul_iff_of_eventually_bounded`
- `subexponentialAtApertureInfinity_mul_iff_of_eventually_bounded`
- `subexponentialAtApertureInfinity_mul_iff_of_tendsto_pos`
- `tendsto_weight_eq_zero_of_mul_upperBound_of_not_upperBound`
- `apertureExponentialUpperBound_finiteShiftPolynomial_iff`
- `apertureExponentialUpperBound_finiteShiftValuation_iff`
- `apertureExponentialUpperBound_finiteShiftPolynomial_complete_iff`
- `finiteShiftPolynomial_eval_zero_of_mul_upperBound_of_not_upperBound`
- `apertureExponentialUpperBound_shiftCoboundary_iff`
- `criticalMellinCompletedError_shiftTwo_subexponential_iff`
- `criticalMellinCompletedError_shiftTwo_upperBound_iff`

## Gates

- [x] corpus and failed-route audit
- [x] paper derivation
- [x] direct Lean checks
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] formal lint attribution audit: no error names either new module; global lint is red on
      unrelated pre-existing umbrella reachability failures
- [x] targeted module build:
      `lake build GaloisForLFunctions.RHTower.CCMEvenShiftExponentialTypeRigidity`
- [ ] external novelty audit
- [ ] RH or whole-lane no-go

## Log

- 2026-07-23 -- Proved exact Gamma desingularization, physical-mode closed form, strict positive
  Gamma budget, completed-error obstruction threshold, full rate-spectrum invariance under stable
  multipliers, necessary boundary collapse for any exponent-changing scalar transport, and the
  complete finite fixed-shift polynomial valuation law. Direct Lean, axiom audit, and targeted
  module build passed. Global formal lint remains red only on unrelated existing umbrella
  reachability failures; neither new module appears in its error list.
