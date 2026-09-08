# Inverse-frequency correction of the critical Bessel response

- **ID:** SELBERG-BESSEL-INVERSE-FREQUENCY-CORRECTION
- **Stage:** 3-formalized
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 17.
- **Scope:** Actual source-defined Bessel functions and their outgoing cusp coefficient. No global spectral inequality is asserted.

## Exact theorem

For the actual dimensionless slope `Q(t)=exp(t)*K_1(exp(t))/K_0(exp(t))`,

`exp(t)<Q(t)<exp(t)+1/2`,

`0<exp(t)+1/2-Q(t)<exp(-t)/8`.

Consequently, for every actual frequency `k=exp(a)>0` and height `Y=exp(T)>0`, the outgoing boundary coefficient satisfies

`k-1/(2*Y)<B(k,Y)<k`,

`0<k-B(k,Y)<1/(8*k*Y^2)`.

Both upper envelopes are proved from the source Riccati equation and positivity, without a Bessel asymptotic expansion or numerical estimate.

## Dependency-closed paper proof

The already-proved source equation is `Q'=Q^2-exp(t)^2`, with `Q>exp(t)`. Put `V=Q-exp(t)>0`. Then

`V'=2*exp(t)*V+V^2-exp(t)`.

The integrating factor `H=exp(-2*exp(t))*(V-1/2)` satisfies

`H'=exp(-2*exp(t))*V^2>0`.

If `V(T)>=1/2`, strict monotonicity of `H` and positivity of its exponential factor force `V(t)>=1/2` for every `t>=T`. On that ray, `V'>=V^2`, so `(1/V+t)'<=0`. Compare this nonincreasing function at `T` and `t=T+1/V(T)+1`: it forces `1/V(t)<=-1`, contradicting `V(t)>0`. Therefore `V<1/2` everywhere.

Now put `D=1/2-V`, so `0<D<1/2` and `D'=2*exp(t)*D-V^2`. The refined factor

`H_2=exp(-2*exp(t))*(D-exp(-t)/8)`

satisfies

`H_2'=exp(-2*exp(t))*(1/4-V^2+exp(-t)/8)>0`.

If `D(T)>=exp(-T)/8`, the same propagation argument gives `D(t)>=exp(-t)/8` for every later `t`. It follows that `D'>=1/4-V^2=D*(1-D)>=D^2`, since `0<D<1/2`. Applying the reciprocal comparison to `1/D+t` again contradicts positivity. Thus `D<exp(-t)/8` everywhere.

Finally, the actual outgoing formula gives `k-B(k,Y)=D(log(k*Y))/Y`. Substituting the two deficit bounds proves the stated physical-height envelopes.

## Lean implementation and audit

Module: `GaloisForLFunctions.RHTower.SelbergBesselBoundaryEnvelope`, namespace `SelbergBesselEnvelope`.

Capstones: `barrier_strictMono`, `excess_lt_half`, `outgoing_bounds`, `refinedBarrier_strictMono`, `deficit_lt_inverse_argument`, `correction_inverse_frequency_bound`, and `outgoing_refined_bounds`.

Complete scratch and final direct source checks passed without warnings. The targeted final build passed, rebuilding only this module (`/tmp/selberg_bessel_envelope_build.log`). Seven capstone checks in the combined scratch audit report only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into the RHTower umbrella and present in the refreshed corpus index. Whitespace checks passed; no Lean or Lake process remained. Repository-wide lint failed on seven unrelated unwired modules, detailed on the parent card; it did not name this module.

## Live consequence to test

At integer Fourier frequencies, the positive correction from `|D_x|` decays as the inverse mode index. This suggests a source-defined compact diagonal correction on square-summable boundary data. The inspected `HTGeometry.BoundedDiagonalOperatorLp` supplies diagonal-operator construction and compactness from cofinite decay. Instantiating it with the actual Bessel coefficients and identifying the full boundary form remain separate proof targets; no such operator identification is assumed here.
