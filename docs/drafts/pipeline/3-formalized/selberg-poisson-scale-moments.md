# Poisson scale moments: rate loss and exact recovery

- **ID:** SELBERG-POISSON-SCALE-MOMENTS
- **Stage:** 3-formalized
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycles 9–10.
- **Scope:** Actual modal set integrals for the existing diagonal Poisson multiplier. No congruence Maass spectral bound is asserted.

## Exact theorem

For every real `s`, set `r=exp(s)>0` and

`d_s(t)=exp(-r*t)-exp(-2*r*t)`.

Both integrands below are integrable on the positive ray, and

`integral_(t>0) d_s(t)^2 dt/t = log(9/8)`,

`integral_(t>0) d_s(t)^2 dt = 1/(12*exp(s))`.

The second moment is injective as a function of `s`, ranges over exactly the positive real numbers, and has no uniform upper bound over unrestricted positive rates. Multiplying it by `exp(s)` gives exactly `1/12`.

The first moment is constant. Thus this modal logarithmic-scale energy alone cannot distinguish small positive rates from large ones. This does not disprove the candidate boundary square-function identity. It prevents incorrectly interpreting that identity alone as a spectral-gap proof.

## Dependency-closed paper proof

Expanding the square gives `exp(-2*r*t)-2*exp(-3*r*t)+exp(-4*r*t)`. After division by `t`, split into the two Frullani differences with rate pairs `(2*r,3*r)` and `(4*r,3*r)`. Their integrals sum to `log(3*r)-log(2*r)+log(3*r)-log(4*r)=log(9/8)`. Their integrability proves integrability of the squared response in logarithmic scale.

In ordinary scale each exponential is integrable, and the resulting value is `1/(2*r)-2/(3*r)+1/(4*r)=1/(12*r)`. Injectivity follows from injectivity of the real exponential. Replacing `s` with `-(u+log(12))` makes this moment equal `exp(u)`, proving the exact positive range and unboundedness.

## Lean implementation

Module: `GaloisForLFunctions.RHTower.SelbergPoissonScaleMoments`.

The implementation uses the actual complex Frullani integral from `HTGeometry.FrullaniIntegral`, takes real parts, proves both integrability statements, and evaluates the actual set integrals. `difference_eq_poissonMultiplier` identifies the response with the dyadic difference of `RHTower.deningerPoissonMultiplier`.

Public capstones include `logScaleEnergy_eq`, `ordinaryScaleEnergy_eq`, `ordinaryScale_rate_recovery`, `ordinaryScaleEnergy_injective`, `range_ordinaryScaleEnergy`, and `ordinaryScaleEnergy_no_uniform_bound`. They take no unproved spectral or arithmetic assumptions.

## Verification

- Scratch name checks and the full scratch proof passed.
- Final direct `lake env lean` check passed without warnings.
- The module is wired into the `RHTower` umbrella.
- Targeted `lake build GaloisForLFunctions.RHTower.SelbergPoissonScaleMoments` passed; only this target was rebuilt. No umbrella build ran.
- Eight capstone axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.
- Index refresh and whitespace checks passed; no Lean/Lake process remained. Repository-wide lint failed on 11 unrelated unwired modules, listed in the parent verification log. It reported no error in this module.

## Next use

Any rate-sensitive bound must use more than the unrestricted diagonal semigroup laws. The parent loop returns to the actual cusp boundary term, testing whether horizontal Fourier energy controls it through a completed-square identity. The congruence-uniform global step remains unproved.
