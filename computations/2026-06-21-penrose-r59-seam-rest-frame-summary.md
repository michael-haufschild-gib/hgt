# R59 — seam rest-frame equalization

**Verdict:** DEAD END / reproduces known FE/Berry lane-equalization.

## Setup
- Seed RandomNode: `Model validation should use out-of-sample bubble-end forecasts, not only retrospective fits to famous crashes`.
- STEP 1 cold list + STEP 2 rng `17`: topic `False-vacuum decay analogies in cosmology`.
- STEP 3 cold list + STEP 4 rng `2`: NODE `The background medium often defines a preferred rest frame, so exact relativistic symmetry is only approximate or emergent`.
- Standing-order target pick: file rng `2` -> `docs/consolidated/01-landscape-and-geometry.md`; topic rng `14` -> seam `Re(s)=1/2` localized many ways.
- STEP 5 constraint: an apparent symmetry can be frame-biased unless tested in the correct completed frame.
- STEP 8 selected transfer by Levenshtein: `completion restores mirror-frame invariance at the critical seam` (`90`).
- STEP 9 method rng `4` = change viewpoint.
- STEP 11 method rng `5` = make visual.

## Computation
Archive script: `computations/2026-06-21-penrose-r59-seam-rest-frame.py`.

The NODE validation used a dispersive analog medium `omega^2=c^2 k^2+alpha k^4`, where phase velocity deviates from `c` increasingly with `k`, confirming a preferred medium frame.

The target test measured mirror-lane magnitude imbalance around the critical seam:

| window | delta | prime-only mean | completed mean |
|---|---:|---:|---:|
| 100-170 | 0.05 | 0.160893 | 1.306464e-16 |
| 100-170 | 0.10 | 0.319867 | 9.364796e-17 |
| 100-170 | 0.20 | 0.625208 | 1.188286e-16 |
| 500-570 | 0.05 | 0.217631 | 3.738329e-16 |
| 500-570 | 0.10 | 0.432490 | 1.027824e-16 |
| 500-570 | 0.20 | 0.847976 | 6.591949e-17 |

## Reading
Prime-only `zeta'/zeta` carries a preferred side; completed `xi'/xi` is mirror-frame invariant at numerical precision. This is correct but already explained by the functional equation and the prior Berry lane-equalization finding. The visual/plot version would not add new content.
