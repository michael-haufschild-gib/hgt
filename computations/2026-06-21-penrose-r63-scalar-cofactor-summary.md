# R63 — scalar-layer cofactor sensitivity

**Verdict:** DEAD END / existing scalar-layer warning.

## Setup
- Seed RandomNode: `Mode conversion at interfaces and defects`.
- STEP 1 cold list + STEP 2 rng `8`: topic `Protein allostery through conformational energy landscapes`.
- STEP 3 cold list + STEP 4 rng `12`: NODE `Metal ions, cofactors, lipids, or post-translational modifications can reshape the landscape and change apparent allosteric mechanisms`.
- Standing-order target pick: file rng `3` -> `docs/consolidated/01-landscape-and-weld-geometry.md`; topic rng `13` -> Scalar Layer.
- STEP 5 constraint: modifiers/cofactors can reshape apparent landscape weights without changing the deeper mechanism.
- STEP 8 selected transfer by Levenshtein: `apparent scalar mechanism is not stable under positive landscape modifiers` (`90`).
- STEP 9 method rng `12` = find invariant.
- STEP 11 method rng `1` = split into subclaims.

## Computation
Archive script: `computations/2026-06-21-penrose-r63-scalar-cofactor.py`.

NODE validation:
- base landscape populations at `T=0.7`: `[0.531, 0.300, 0.169]`;
- with cofactor shift: `[0.264, 0.538, 0.198]`.

Target test on `sigma=0.3`, window `100-170`:
- smooth positive cofactor shifted scalar `beta=log(1+|P|)` by mean `0.214508`, range `0.000283..0.430386`;
- phase shift max `4.441e-16`;
- `cos(A,P)` shift max `3.331e-16`.

## Split-subclaim Check
- Scalar amplitude is not invariant under positive modifiers: true.
- Phase direction and relative-angle observables are invariant under positive scalar modifiers: true.
- New HGT content: false; this is exactly why the Scalar Layer is marked useful but misleading.

## Reading
The Scalar Layer should not be used as a mechanism readout without phase/weld controls. Correct but already in the target statement.
