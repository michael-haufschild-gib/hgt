# Positive natural-band divisor profile

- **ID:** pm-ramanujan-band-profile
- **Stage:** 3-formalized
- **Route:** PM
- **Source:** `../1-in-progress/pm-ramanujan-band-critical-profile.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PMRamanujanBandProfile.lean`

For epsilon>0 let `g(p)=p/(p+1-p^(-epsilon))`,
`f(n)=prod_(p|n)(1-g(p))` for n>0, f(0)=0, and
`F(N)=sum_(n<=N)f(n)`. The exact finite identity is

`F(N)=sum_(d<=N) mu(d)*prod_(p|d)g(p)*floor(N/d)`.

For every delta>0, `sum_n f(n)*n^(-delta)` converges. Indeed the local
positive Euler tail is `(1-g(p))*p^(-delta)/(1-p^(-delta))`, with
`0<1-g(p)<=1/p`; the local product is bounded by a summable exponential
majorant. Therefore `F(N)<=C_delta*N^delta`, F>=0, F(1)=1, and
`sum_N F(N)^2/[N(N+1)]` converges.

The mathematical hypotheses are only positivity of the damping/exponent
parameters. No RH premise, new axiom, computation, or heartbeat increase
enters the proof. This is the candidate profile's admission theorem;
actual band convergence to this profile and moving remainder energy are
not proved by this module.

## Validation

All 13 public declarations: `propext`, `Classical.choice`, `Quot.sound`
only, checked in /tmp. Clean combined scratch audit subsequently exited0.
`lake --old build GaloisForLFunctions.RHTower.PMRamanujanBandProfile`
passed; only this new leaf built (106s). Umbrella import added.
Final `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandProfile.lean`
passed with no diagnostics. No full or umbrella build ran.
Global lint reported twelve unrelated missing umbrella imports, listed
on the active source card; no finding concerned this module.
