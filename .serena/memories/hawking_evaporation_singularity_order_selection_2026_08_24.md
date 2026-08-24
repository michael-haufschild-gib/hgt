# Hawking evaporation-singularity order selection (2026-08-24)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingEvaporationSingularityOrderSelectionEndpoint.lean`; wired into `formal/GaloisForLFunctions/RHTower.lean` at import line 12538. No git commands used.

New Hawking-specific route (not cubic/passivity relabeling): in semiclassical Schwarzschild mass loss `dM/du = -alpha/M^2`, remaining lifetime is `M^3/(3 alpha)` and surface gravity is `kappa=1/(4M)`. On dyadic masses `M_n=2^{-n}`, exact shell duration is `7 M_n^3/(24 alpha)`. If a sector first appears at exact full-mirror coupling order `m` and endpoint intensity scales as `kappa^(2m)`, shell load is a fixed positive factor times `(2^(2m)/8)^n`.

Lean proves:
- exact dyadic mass/shell-duration identities;
- exact physical-load factorization;
- order 1 load is geometric `(1/2)^n`, hence summable;
- every order `m>=2` has each term >=1, hence nonsummable;
- positive finite endpoint load forces order one;
- finite terminal cutoff is summable for every order (sharp falsification boundary);
- `ThetaCuspHawkingSchwarzschildEndpointFiniteLoad ↔ ThetaCuspHawkingFullMirrorNoOrderJump`;
- therefore `RiemannHypothesis ↔ ThetaCuspHawkingSchwarzschildEndpointFiniteLoad` and finite load excludes off-critical Xi copies.

Epistemic boundary is explicit in file header: physical weld is unproved. Exact theta-mirror coupling order is a weak-coupling notion, while surface gravity diverges at `M→0`; need dimensionless calibration and strong-coupling/quantum-gravity control. Remnant/Planck cutoff or strong-coupling saturation kills selector. This is remaining black-hole-dynamics producer.

Verification:
- direct compile passed: `cd formal && lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingEvaporationSingularityOrderSelectionEndpoint.lean`;
- `#print axioms` for all 14 new theorems: only `propext`, `Classical.choice`, `Quot.sound`;
- lint found no source-level forbidden declarations in new file but global lint remains blocked by pre-existing unreachable owned module `GaloisForLFunctions.HTGeometry.LocallyIntegrableLinearEvolution` from `GaloisForLFunctions.HTGeometry`;
- `/tmp` scratch removed; no build artifact for new module remained.

Primary literature inspirations used: standard Schwarzschild evaporation/Page treatments; Bianchi–Smerlak entropy/energy tension; Lowe–Thorlacius 2026 semiclassical-breakdown/thunderbolt result reinforces that endpoint extrapolation is a real physical risk, not a closed theorem.