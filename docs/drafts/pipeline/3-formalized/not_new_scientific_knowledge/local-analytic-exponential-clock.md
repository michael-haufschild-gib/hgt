# Local analytic exponential clocks preserve hypertranscendence

- **ID:** `local-analytic-exponential-clock`
- **Status:** FORMALISED IN LEAN 4
- **Type:** local meromorphic carrier theorem / observability bridge
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/LocalAnalyticExponentialClock.lean`
- **Scientific novelty:** not claimed; corpus value is a concrete local realization that discharges
  an abstract response hypothesis

## Statement

Let `U` be a nonempty connected open subset of the complex plane and let `f` be analytic on `U`.
Both `f` and its pointwise exponential define genuine elements of the meromorphic fraction field
`M(U)`.  Lean proves

\[
  \exp(f)\ne0,
  \qquad
  \frac{\mathrm d\exp(f)}{\exp(f)}=\mathrm df
\]

inside the differential field `M(U)`.  It also proves that the canonical embedding
`C(z) -> M(U)` commutes with differentiation, making `M(U)` a differential algebra over the
rational coordinate field.  Therefore

\[
  f\text{ HT over }C(z)
  \quad\Longrightarrow\quad
  e^f\text{ HT over }C(z).
\]

Every nondegenerate affine readout `c (b exp(f) - 1)` with nonzero `b,c in C(z)` is HT as well.

## Exact Lean surface

The analytic and carrier-level declarations are:

- `analyticFunctionElement`;
- `analyticExponentialElement`;
- `analyticSubringDeriv_analyticExponentialElement`;
- `analyticExponentialElement_ne_zero`;
- `analyticExponentialMero_ne_zero`;
- `analyticExponentialMero_logDeriv`.

The local rational-coordinate and HT declarations are:

- `meroField_deriv_ratfuncToMero_on`;
- `meroFieldRatFuncDifferentialAlgebra`;
- `hypertranscendentalOver_analyticExponentialMero`;
- `hypertranscendentalOver_analyticExponentialAffineMero`.

The result uses the previously formalized abstract theorem
`hypertranscendentalOver_phase_of_logDeriv_eq_deriv`, but it no longer asks an application to
assume the logarithmic-derivative equation.  Complex analysis proves that equation for the actual
pointwise exponential on the chart.

## Direct corpus applications

This closes a reusable gap between global HT sources and local physical observations:

1. `hypertranscendentalOver_restrictMeroAlgHomRatFunc` restricts a global meromorphic HT source to
   a pole-free connected observation chart;
2. the new local `C(z)` differential-algebra structure makes the restricted chart a valid carrier
   for the general HT observability theorems;
3. once the restricted source is identified with an analytic representative `f`, the actual
   exponential phase and every nondegenerate affine readout inherit HT automatically.

This applies without changing the theorem to exponential phases used by scattering responses,
interferometric and relational clocks, scalar-field clock charts, neural exponential gates, and
sigmoidal gene-regulatory reporters.  The physics interpretation motivates the observation class;
the formal statement is an exact theorem about values and local analytic germs.

`BlackHoleDressedLogSpectralClock.lean` now specializes the result in
`hypertranscendentalOver_blackHoleHigherMultipoleLocalAnalyticResponse`: an analytic HT exponent on
a local chart produces an actual exponential phase whose nondegenerate Schwarzschild
higher-multipole readout is HT.

## No-go and significant positive replacement

**No-go.** Exponentiating a globally meromorphic function with poles generally creates essential
singularities, so the exponential need not belong to the same global meromorphic field.  A global
carrier theorem of that form would be false.

**Positive theorem.** On every pole-free analytic observation chart, the exponential is a genuine
nonzero meromorphic-field element, its logarithmic derivative is exact, and HT passes through the
phase and its nondegenerate affine readouts.  The obstruction is global singularity structure, not
loss of clock information at the local observer.

## RH pressure test

This does not create an RH sign or a new source.  It strengthens source transport: any global
Gamma, elliptic-Gamma, Dirichlet, or future Euler-prime HT element that is restricted and identified
analytically on a physical chart can now be passed through an actual exponential response without
retaining an unproved logarithmic-derivative hypothesis.  It removes an observer-channel
hypothesis, but it remains a consumer of an HT source rather than the missing positive prime-side
producer.

## Verification

- exact target cache: `lake build +GaloisForLFunctions.HTGeometry.LocalAnalyticExponentialClock`
- direct file check: `lake env lean GaloisForLFunctions/HTGeometry/LocalAnalyticExponentialClock.lean`
- dependent application check:
  `lake env lean GaloisForLFunctions/HTGeometry/BlackHoleDressedLogSpectralClock.lean`
- no numerical computation and no full build
