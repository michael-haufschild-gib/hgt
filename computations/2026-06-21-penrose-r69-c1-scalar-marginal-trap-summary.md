# R69 — C1 scalar marginal trap

**Verdict:** DEAD END / generic reason C1 exists.

## Setup
- Seed RandomNode: `The sol-gel transition may be gradual and path-dependent rather than a sharp thermodynamic phase boundary`.
- STEP 1 cold list + STEP 2 rng `12`: topic `Fractional Brownian motion in anomalous diffusion`.
- STEP 3 cold list + STEP 4 rng `5`: NODE `The probability density remains Gaussian while its variance scales as t^(2H)`.
- Standing-order target pick: file rng `1` -> `docs/consolidated/08-conjectures-required.md`; topic rng `1` -> `C1 — carrier is an oriented 2-form, not a scalar`.
- STEP 5 constraint: scalar marginal shape can miss the real transport structure.
- STEP 8 selected transfer by Levenshtein: `C1 needs area orientation not Gaussian scalar samples` (`55`).
- STEP 9 method rng `10` = test extreme cases.
- STEP 11 method rng `12` = find invariant.

## Computation
Archive script: `computations/2026-06-21-penrose-r69-c1-scalar-marginal-trap.py`.

NODE validation:
- Gaussian samples with variance `t^(2H)` gave fitted exponents `0.594`, `1.005`, `1.600` for `H=0.3,0.5,0.8`.

Target extreme case:
- `zeta'/zeta` phase-space trace at `sigma=0.3`, window `100-170`;
- time reversal preserved scalar amplitude samples exactly:
  - mean original `1.433167`, reversed `1.433167`;
  - sorted scalar maxdiff `0`;
- oriented area flipped:
  - original `5.632610`;
  - reversed `-5.632610`.

## Invariant
The scalar distribution is not the invariant. The oriented area/two-form is.

## Reading
This confirms the C1 warning, but it is not new mathematics: it is the generic reason an oriented carrier is needed.
