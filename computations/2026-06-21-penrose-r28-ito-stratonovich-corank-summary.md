# Penrose R28 — Ito/Stratonovich Corank Transfer

Random path:
- Seed RandomNode: `Distinction between annealed and quenched averaging`.
- Step 1/2 topic: `Stochastic resonance in nonlinear dynamics` (rng 12).
- Step 3/4 NODE: `The noise interpretation, Ito versus Stratonovich, can change results in systems with state-dependent noise` (rng 17).
- Standing-order target: `docs/consolidated/01-landscape-and-geometry.md` (rng 2), candidate 9 (rng 9): `(G4) weight/Tate torus: dim W = corank`.

Node validation:
- Same written SDE `dX = mu X dt + sigma X dW` with state-dependent noise:
  - Ito mean log `-0.326797`, theory `-0.321250`.
  - Stratonovich mean log `0.034682`, theory `0.040000`.
  - Mean `X`: Ito `1.043604`, Stratonovich `1.497541`.

Step 8:
- Levenshtein selected `ito_stratonovich_weight_torus_corank` (`19`) over `state_dependent_phase_noise_dimW` (`28`) and `stochastic_calculus_prime_log_connection` (`32`).

Step 9, method 10 (`Test extreme cases`):
- Constant-noise control gave zero rank correction for all windows/cutoffs.
- True completed carrier had Stratonovich-minus-Ito effective-rank correction much larger than finite/random controls:
  - `[100,170]`, `N=30`: true `+1.8593`; finite `+0.2181`; random `+0.2323`.
  - `[100,170]`, `N=100`: true `+2.2157`; finite `+0.3876`; random `-0.0504`.
  - `[500,570]`, `N=60`: true `+1.5671`; finite `+0.0813`; random `+0.4519`.
  - `[900,970]`, `N=60`: true `+1.7992`; finite `+0.1279`; random `+0.0285`.

Step 11, method 9 (`Test small cases`):
- The correction is not only a large-N artifact. True/control ratios:
  - `[100,170]`, `N=5`: true `+0.3872`, finite `+0.1061`, random `+0.0088`, ratio `3.65`.
  - `[100,170]`, `N=20`: true `+1.4594`, finite `+0.1644`, random `+0.1022`, ratio `8.88`.
  - `[900,970]`, `N=100`: true `+1.6085`, finite `-0.2324`, random `+0.0780`, ratio `6.92`.
- One leakage row: `[500,570]`, `N=30`, random `+0.8654` versus true `+1.2841`.

Step 12 battery:
- Tested sigma lanes `.3/.5/.7/1.2` at `N=80`, with shuffled true coefficient control.
- Summary: `total=12`, `pass_true=5`, `pass_shuffle=8`.
- Clean regime:
  - Sigma `.5`: true passed all three windows against finite/random controls (`+2.0523`, `+1.4566`, `+1.6191`).
  - Sigma `.7`: true passed two of three; one random leakage row at `[500,570]`.
- Boundary failures:
  - Sigma `.3` weak in all windows.
  - Sigma `1.2` collapsed in all windows; true and finite/random comparable.

Promptability audit:
- Cold prompt predicted the broad story: Ito gives a correction/drift/anomaly, Stratonovich is geometric, constant noise recovers `dim W = corank`.
- The counted content is narrower: the actual correction is not generic nonconstant-noise behavior; it is localized to the true completed carrier around the seam/middle lanes, mostly absent in finite/random controls, and collapses in the Euler-convergent strip.

Finding:
- `[EXPERIMENTAL FINDING / CONJECTURE]` For finite prime-weight torus carriers, the Stratonovich midpoint interpretation recovers roughly 1.5--2.2 more effective rank than the Ito-left interpretation on the true completed carrier near the seam, while finite/random controls have small or leaky corrections and constant noise has none. This gives a bounded experimental warning for the `dim W = corank` face: state-dependent continuum completion can change the observed finite corank/rank, and the effect is seam-local rather than universal.
