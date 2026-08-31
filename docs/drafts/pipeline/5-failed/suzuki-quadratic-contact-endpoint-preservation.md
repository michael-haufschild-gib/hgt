# Suzuki quadratic-contact endpoint preservation

- **ID:** SUZ-QCEP
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** shared HB/FZZ-P/PW-B/RBH Ward producer · signed transition-core compensation
- **Statement:** Replacing the first-contact aligned residual `E_N` by the quadratic-contact residual `E_N^2/C_N` preserves the zero-width CCM continuation needed for RH.

## Exact killing theorem/mechanism

The claim is false for the compensation/CCM-abscissa mechanism.  Eventual boundedness of
`E_N^2/C_N` yields `G_N=O(N^(1/4))`, then `Q(t)=O(exp(t/4))`.  The tilted Laplace transform is
holomorphic on `Re z>1/4`, so the critical-Mellin defect reaches only `Re u>-1/4`.  Rotated Xi
tomography therefore supplies `XiZeroHalfPlaneBound (1/4)`, i.e. `Re rho≤3/4`, rather than the
zero-width endpoint equivalent to RH.

This kill is scoped precisely: higher contact cannot be treated as endpoint-preserving using only
the resulting growth envelope and CCM continuation.  Any surviving quadratic-contact proof must
add new cancellation that improves the envelope back to exponent zero.

## Strongest positive survivor

For every `0≤alpha<1/2`,

`|Q(t)| ≤ B exp(alpha t)` for `t≥0` implies `XiZeroHalfPlaneBound alpha`.

The actual quadratic Suzuki residual instantiates this at `alpha=1/4`.  This is a new quantitative
resolvent-width theorem, not a restated negation.

## Lean status

- `CCMCriticalMellinResolventExponentialWidth.lean`
  - `xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventSource_exponentialBound`
  - `xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventExponentialBounded`
- `SuzukiTransitionCoreQuadraticContactWidthLoss.lean`
  - `xiZeroHalfPlaneBound_quarter_of_suzukiTransitionCoreQuadraticContactResidualEventuallyBounded`
  - `suzukiTransitionCore_linear_quadratic_contact_widthClassification`

Targeted builds pass.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Consequence for four-route chain

First contact remains unique among the first two contact orders in reaching the RH endpoint through
this mechanism.  Quadratic contact is not a free nonlinear repair: it spends one quarter-plane.
Remaining producer must prove first-order aligned-energy boundedness or supply genuinely new
arithmetic cancellation that removes the quarter-power growth.
