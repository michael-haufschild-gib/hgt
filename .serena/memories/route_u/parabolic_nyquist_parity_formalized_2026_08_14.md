# Route U parabolic Nyquist parity formalized (2026-08-14)

New module: `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeParabolicNyquistParity.lean`.

Premise-free Lean results for every compact approximation n, Schwartz profile f, and positive parabolic shell coordinate u:
- exact complex hard-edge periodization under subtraction of one alias period;
- coarse-even sample tends `(1/2) F_n(-4/u)`;
- full fine sample tends `0`;
- odd sample tends `-(1/2) F_n(-4/u)`;
- pair tends to antisymmetric ultraviolet parity line `(1,-1)`.

Core declarations:
- `routeUComplexHardEdgePeriodizationAt_sub_aliasPeriod`
- `tendsto_routeUDyadicParabolicEvenSample`
- `tendsto_routeUDyadicParabolicFullSample_zero`
- `tendsto_routeUDyadicParabolicOddSample`
- `tendsto_routeUDyadicParabolicParityPair`

Verification:
- scratch and tree `lake env lean` passed;
- exact Lake-path module olean built directly (no lake build);
- four limit theorems audit to only `[propext, Classical.choice, Quot.sound]`;
- no sorry/admit/axiom/opaque/unsafe/native_decide/#eval/#reduce;
- umbrella import wired but umbrella not built.

Research card updated:
`docs/drafts/pipeline/1-in-progress/new_scientific_knowledge/route-u-parabolic-nyquist-alias-covariance.md`.

Remaining hard core: compact-u and full-strip uniform version, multiplicity-exact Xi Riemann-von Mangoldt, low/high shell tightness, normalized covariance, then prime-Gamma finite-part analysis. This theorem proves local UV parity is genuinely (1,-1), not conjectural.