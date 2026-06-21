# R60 — Berry seam coarse-graining warning

**Verdict:** DEAD END / weakened restatement of Berry seam result.

## Setup
- Seed RandomNode: `The background medium often defines a preferred rest frame, so exact relativistic symmetry is only approximate or emergent`.
- STEP 1 cold list + STEP 2 rng `11`: topic `Cellular automaton interpretations of physics`.
- STEP 3 cold list + STEP 4 rng `6`: NODE `Coarse-graining can erase microscopic determinism, but it can also introduce artifacts mistaken for physical laws`.
- Standing-order target pick: file rng `3` -> `docs/consolidated/01-landscape-and-weld-geometry.md`; topic rng `18` -> Berry seam layer.
- STEP 5 constraint: coarse-graining can erase the actual microscopic carrier and leave an artifact.
- STEP 8 selected transfer by Levenshtein: `coarse-graining mirror lanes erases Berry relative phase` (`75`).
- STEP 9 method rng `14` = weaken.
- STEP 11 method rng `12` = find invariant.

## Computation
Archive script: `computations/2026-06-21-penrose-r60-berry-coarse-grain.py`.

NODE validation used deterministic Rule 90:
- microscopic rule was deterministic XOR;
- density range over time `0.0083..0.2645`;
- block entropy range `0.0400..0.5762`.

Target test compared completed mirror lanes before and after coarse-graining:
- magnitude imbalance stayed numerical zero (`~1e-16`);
- median relative phase was large and lane-resolved: `0.7105`, `1.2337`, `1.9306` for deltas `0.05`, `0.10`, `0.20` on `[100,170]`;
- lane averaging caused substantial cancellation: median cancellation `0.0624`, `0.1843`, `0.4315`, with max cancellation up to `0.9493`.

## Invariant
The invariant is the lane-resolved Berry relative phase. Averaging the mirror lanes before reading it loses the signal.

## Reading
The warning is correct but not new. It is a weakened restatement of the existing Berry seam result: completion equalizes mirror-lane magnitudes and moves the residual into relative phase.
