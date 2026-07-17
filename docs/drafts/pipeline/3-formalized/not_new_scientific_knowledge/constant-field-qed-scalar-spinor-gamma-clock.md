# Constant-field QED scalar/spinor determinants form a noncancelling Gamma clock

- **ID:** `constant-field-qed-scalar-spinor-gamma-clock`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PROVEN]` exact two-dimensional constant-field QED value relations and unconditional HT consequences; `[BRIDGE]` Gamma-orbit, Veneziano-ratio, and Gauss-duplication synthesis
- **Source:** S. K. Blau, M. Visser, and A. Wipf, *Analytic Results for the Effective Action*, arXiv:0906.2851, equations (20) and (29)
- **Statement:** After removing explicit DA renormalization gauges, the scalar and spinor one-loop determinant carriers are `Gamma(x+1/2)` and `Gamma(x+1)`; their quotient and product are both HT, and their product is one double-scale Gamma clock up to a nonzero DA gauge.

## Goal

Turn the exact bosonic/fermionic Landau-level shift into a reusable corpus theorem.  The observed
coordinate is the dimensionless mass-to-field ratio `x=m^2/(2B)`, not physical time evolution.

## Gates

- [x] 0 → 1 in-progress: primary-source values extracted and existing APIs identified
- [x] 1 → 2 fully-proven: quotient, product, duplication, and DA-renormalization obstruction
- [x] 2 → 3 formalized: direct Lean check and axiom audit
- [ ] 3 → 4 publication-ready: standalone exposition not written

## Approach

Define the renormalized exponentiated Gamma carriers

`S(x)=Gamma(x+1/2)`, `F(x)=Gamma(x+1)`.

Then:

1. `F/S` is the inverse reduced Veneziano ratio with separation `1/2`, hence HT.
2. `S*F` is a same-orientation positive Gamma pair, hence HT without any separation premise.
3. Gauss duplication identifies `S*F` with `Gamma(2x+1)` up to the standard nonzero DA gauge.
4. Since `F/S` is HT, no DA renormalization gauge can transform the scalar carrier into the
   spinor carrier.

## Exact theorem surface

The Lean certificate proves unconditionally:

1. `F/S = reducedVenezianoAmplitudeMero (1/2) (1/2)⁻¹`.
2. `F/S` is hypertranscendental over `RatFunc ℂ`.
3. `S*F = gammaPositiveShiftPairMero (1/2) 1`, and this product is
   hypertranscendental over `RatFunc ℂ`.
4. `S*F = (gammaNatScaleGaussGaugeMero 2 1)⁻¹ * gammaNatScaleMero 2 1`.
5. For every differentially algebraic meromorphic `g`, `F ≠ g*S`.
6. `F/S` is not the meromorphic image of any rational function.
7. Every scalar-aware finite differential circuit presenting `F/S` has an HT non-scalar atom.

The fifth item is the nontrivial positive statement surviving the cancellation question: the
half-integer scalar shift and the integer spinor shift define inequivalent determinant carriers
even after arbitrary DA multiplicative renormalization.

## Existing-corpus value

This module applies, rather than restates, four previously independent theorem surfaces:

- the nonintegral-shift criterion for reduced Veneziano/Gamma ratios;
- unconditional HT for same-orientation Gamma pairs;
- the exact meromorphic Gauss multiplication law and its nonzero DA gauge;
- HT-source extraction from finite differential circuits.

Thus one physical pair of exact values closes those APIs into a single reusable comparison theorem.
The duplication equality also transports the combined scalar--spinor response from two unit-slope
clocks to one double-scale Gamma clock without losing HT information.

## Scope and RH pressure test

The clock is the observable parameter `x=m^2/(2B)`.  Nothing here treats laboratory time as a flow.
The result strengthens the corpus model that HT records distinguishability of parameter-reading
orbits under admissible DA gauges.

For the RH search, this is an archimedean cancellation and scale-transport theorem.  It can rule
out proposed DA identifications of Gamma-type completion factors and can normalize a paired Gamma
sector to one double-scale carrier.  It supplies neither prime arithmetic nor zero-location
positivity, so it is not by itself an RH source theorem.

## Lean certificate

- `formal/GaloisForLFunctions/HTGeometry/ConstantFieldQEDGammaClock.lean`
- Exact target build completed successfully.
- Direct single-file Lean check completed successfully.
- The capstone axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- The Lean source contains no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` token.

## Log

- 2026-07-17 -- exact QED values and three existing theorem surfaces isolated; formalization started.
- 2026-07-17 -- all seven theorem surfaces formalized and narrowly verified; promoted to stage 3.
