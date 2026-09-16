# Complete original forcing of the corrected future field

Target: identify the full original source in the weak equation of
`timeLiftField + originalFutureResponse - capBoundaryField`, as required
for full temporal/metric/left-QNM matching. That matching and RH remain open.

[BRIDGE] Lean proved: for every general joint smooth compact physical test,
the corrected original field pairs with `weakWaveTest` to give exactly the
hyperbolic-area pairing of `timeOriginalForcing` with the test.

For `r=((tau,x),X+i*k)`, set `U = timeLiftField + response - capBoundaryField`.
For every joint smooth compact `Phi` with `tsupport Phi` contained in `x<0`,

```
integral U(r) * weakWaveTest(Phi)(r)
  = integral exp(-k) * timeOriginalForcing(q,branch,a,tau,x,[X,exp(k)]) * Phi(r).
```

The test operator retains both temporal/radial second derivatives and the
full angular transpose with coefficient `1/cosh(x)^2`. Neither separable
tests nor a postulated wave equation are used.

Existing exact inputs: EQ proves the actual future response's reduced weak
wave equation; ER proves the original cap homogeneous; the older
`timeOriginalForcing_gradient_absorption` already identifies the pointwise
wave of the original lift plus the complete reduced source with the
original forcing. Do not rederive or replace that source identity.

Dependency-closed proof:

1. Apply temporal integration by parts to the original smooth lifted radial
   coefficient and joint test slices. Apply the existing angular
   transposition at zero circle radius to the full theta half-square.
2. Admit the target Fubini interchanges by joint compact support. Identify
   the result with the existing actual `timeFieldWave` of the original lift,
   including `1-radialUnit(x)^2 = 1/cosh(x)^2`.
3. Convert the reduced forcing's source-event integral to the full target
   pairing. On physical `x<0`, negative static time implies pre-onset
   `tau+x<0`; outside that half-plane the test vanishes.
4. Add the lift and reduced response equations, subtract the homogeneous
   cap, and apply the original gradient-absorption identity pointwise.

All source and field pairings require absolute admission. No separability,
wave-equation, forcing-identification or matching premise may be supplied.
The Lean proof supplies this admission separately for the original lift,
actual infinite response, original cap and complete original forcing.

**Whole-route consequence:** the corrected original future field has exactly
the original bulk source, including the onset cross term and angular
gradient contribution. This is a bulk weak equation. It does not identify
the complete reconstructed metric/current, justify a noncompact left-QNM
test, or establish the required boundary action. Those matching obligations
and RH remain open. The separated stationary metric theorem does not by
itself reconstruct this time-dependent infinite future field.

**Formal status:**
[CompleteOriginalWeakSource](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCompleteOriginalWeakSource.lean),
namespace `RHTower.D4BMCompleteOriginalWeakSource`:
`original_lift_weak_wave`, `reduced_forcing_target_pair`,
`original_forcing_test_integrable`, `corrected_future_test_integrable`,
and `complete_original_weak_wave`.
Scratch check passed without errors or warnings. Exact leaf audit passed
in 16.93 seconds, two jobs. Umbrella import wired; no umbrella build.
Global lint reports the pre-existing unrelated unwired
`ThetaCuspHawkingBMOnsetTransgressionHorizon`; no new-module lint error.
