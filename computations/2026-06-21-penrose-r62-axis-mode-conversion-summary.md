# R62 — two-axis mode-conversion witness

**Verdict:** DEAD END / existing two-axis orthogonality witness.

## Setup
- Seed RandomNode: `Spectral artifacts can appear from synchronous updating`.
- STEP 1 cold list + STEP 2 rng `12`: topic `Artificial band gaps in phononic metamaterials`.
- STEP 3 cold list + STEP 4 rng `6`: NODE `Mode conversion at interfaces and defects`.
- Standing-order target pick: file rng `2` -> `docs/consolidated/01-landscape-and-geometry.md`; topic rng `21` -> two orthogonal axes.
- STEP 5 constraint: defects/interfaces can convert signal between modes; a single observed mode is not the whole physics.
- STEP 8 selected transfer by Levenshtein: `interface conversion separates constraint and localization axes` (`38`).
- STEP 9 method rng `21` = dependency chain.
- STEP 11 method rng `7` = strip to essentials.

## Computation
Archive script: `computations/2026-06-21-penrose-r62-axis-mode-conversion.py`.

NODE validation used a two-mode interface toy: same-mode transmission `1/(1+kappa^2)` and converted fraction `kappa^2/(1+kappa^2)`.

Target test used an FE-symmetric off-line quartet polynomial. It preserves the weld/constraint axis while failing positivity/localization:

| a | FE residual max | center curvature | expected `2/a^2` |
|---:|---:|---:|---:|
| 0.03 | 2.274e-13 | 2222.208627 | 2222.222222 |
| 0.06 | 2.842e-13 | 555.553534 | 555.555556 |
| 0.12 | 2.542e-13 | 138.887591 | 138.888889 |
| 0.24 | 2.274e-13 | 34.720969 | 34.722222 |

## Essential Core
FE/weld symmetry can hold exactly while the positivity axis fails. The off-line quartet is the minimal witness.

## Reading
The NODE gives a good metaphor for avoiding axis collapse, but the mathematics is the already-banked orthogonality: weld/constraint does not force RH-positivity.
