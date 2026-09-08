# Sharp trace-constrained critical cusp energy

- **ID:** SELBERG-SHARP-CUSP-TRACE-INFIMUM
- **Stage:** 3-formalized
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 16.
- **Scope:** Actual critical Bessel response and compact real C¹ logarithmic-height profiles. No automorphic extension or compact-core positivity is assumed.

## Exact theorem

Let `G(a,t)=exp(t/2)*K_0(exp(a+t))` be the actual critical mode, and let `B(a,T)` be its actual outgoing boundary coefficient. Write

`E_(a,T)(f)=integral_(t>T) exp(-t)*(f'^2+(exp(a+t)^2-1/4)*f^2)`.

Then

`inf { E_(a,T)(f) : f compact real C¹, f(T)=1 } = B(a,T)`.

The theorem supplies actual compact approximants and a greatest-lower-bound proof, including nonemptiness of the energy set. Consequently

`exists compact f with E_(a,T)(f)<0` if and only if `a+T<tau`,

and every compact profile has nonnegative excess if and only if `a+T>=tau`. Thus the isolated-tail cutoff from cycle 14 is now proved both necessary and sufficient.

## Dependency-closed paper proof

The source derivative `K_0'=-K_1<0` makes `K_0(exp(a+t))` decreasing. The actual critical mode satisfies `G'=(1/2-Q(a+t))*G`, and the previous exact boundary identity is

`E(f)=integral_(t>T) exp(-t)*(f'-(1/2-Q(a+t))*f)^2 + B(a,T)*f(T)^2`.

Choose once a compact C¹ function `beta` with `beta(0)=1`, using the inspected smooth-bump existence theorem. Its derivative is continuous with compact support. Let `J=integral beta'^2`, and for `L=exp(ell)>0` define

`f_ell(t)=beta((t-T)/L)*G(a,t)/G(a,T)`.

Affine rescaling preserves compact support, the product is C¹, and `f_ell(T)=1`. Differentiating the product cancels the critical-mode part of the square remainder exactly. The remaining square is

`exp(-t)*(G(a,t)/G(a,T))^2 * (beta'((t-T)/L)/L)^2`.

For `t>=T`, monotonicity of `K_0` and the identity `exp(-t)*G(a,t)^2=K_0(exp(a+t))^2` bound the first factor by `exp(-T)`. The exact full-line change of variables gives

`integral (beta'((t-T)/L)/L)^2 = J/L`.

Every relevant integrand is proved integrable. Enlarging the tail integral to the full line therefore gives the frequency-independent bound

`0<=E(f_ell)-B(a,T)<=exp(-T)*J/exp(ell)`.

For any positive tolerance `exp(e)`, the explicit choice `ell=log(1+exp(-T)*J/exp(e))` makes the upper error strictly smaller than that tolerance. The exact boundary identity gives the lower bound for every unit-trace profile, so this establishes the infimum and greatest-lower-bound properties.

If `B(a,T)<0`, choose tolerance `-B(a,T)` to obtain a compact unit-trace profile with strictly negative excess. Conversely the boundary identity excludes negative excess when `B(a,T)>=0`. The already-proved Bessel sign classification gives both cutoff equivalences.

## Lean implementation and audit

Module: `GaloisForLFunctions.RHTower.SelbergBesselBoundaryTrace`, namespace `SelbergBesselTrace`.

Capstones: `approximation_trace`, `approximation_hasDerivAt`, `integral_cutoffSlope_sq`, `approximation_remainder_bound`, `unit_trace_approximation`, `outgoing_isGLB`, `trace_energy_inf`, `negative_energy_iff`, and `all_compact_energies_nonneg_iff`.

Complete scratch and final direct checks passed without warnings. The targeted final build passed, rebuilding only this module (`/tmp/selberg_bessel_trace_build.log`). Eleven capstone checks in the combined scratch audit report only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into the RHTower umbrella and present in the refreshed corpus index. Whitespace checks passed; no Lean or Lake process remained. Repository-wide lint failed on seven unrelated unwired modules, detailed on the parent card; it did not name this module.

## Consequence for the active route

This identifies the exact isolated cusp response, rather than a one-sided energy estimate. The approximation error is independent of frequency, which is useful for simultaneous mode approximation. Infinite Fourier assembly, the actual congruence core boundary form, and the sign of their coupling still require proof. The compact negative tests here are not global automorphic counterexamples.
