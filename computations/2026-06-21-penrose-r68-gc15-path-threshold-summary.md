# R68 — G-C15 path-dependent thresholds

**Verdict:** DEAD END / proof-obligation warning.

## Setup
- Seed RandomNode: `Slime or EPS layers acting as transient lubricants`.
- STEP 1 cold list + STEP 2 rng `4`: topic `Thixotropic gel phase transitions`.
- STEP 3 cold list + STEP 4 rng `6`: NODE `The sol-gel transition may be gradual and path-dependent rather than a sharp thermodynamic phase boundary`.
- Standing-order target pick: file rng `1` -> `docs/consolidated/08-conjectures-required.md`; topic rng `26` -> `G-C15. One object, two entrances`.
- STEP 5 constraint: route-dependent thresholds do not prove an intrinsic phase/object boundary.
- STEP 8 selected transfer by Levenshtein: `two entrances can have path-dependent transition lags` (`68`).
- STEP 9 method rng `18` = right theorem.
- STEP 11 method rng `7` = strip to essentials.

## Computation
Archive script: `computations/2026-06-21-penrose-r68-gc15-path-threshold.py`.

NODE validation:
- up-ramp apparent transition at `x=0.60`;
- down-ramp apparent transition at `x=0.50`.

Target test:
- intrinsic negative index changed at the true object threshold;
- two entrance readouts had path-dependent lags and disagreed near threshold.

Example rows:
- up path, `x=0.45`: intrinsic `1`, entrance A `0`, entrance B `1`;
- up path, `x=0.50`: intrinsic `0`, entrance A `0`, entrance B `1`;
- down path, `x=0.50`: intrinsic `0`, entrance A `1`, entrance B `0`.

## Essential Core
The right G-C15 theorem must identify a shared intrinsic carrier/index. Similar route thresholds or synchronized onset are not evidence.

## Reading
This is a useful proof-obligation warning, but it does not advance G-C15.
