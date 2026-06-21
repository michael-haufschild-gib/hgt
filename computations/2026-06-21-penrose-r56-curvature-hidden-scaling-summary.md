# R56 — off-line curvature hidden scaling

**Verdict:** DEAD END / overlaps existing localization and grid-stability cards.

## Setup
- Seed RandomNode: `The unstable composition range lies inside the spinodal, not merely inside the miscibility gap`.
- STEP 1 cold list + STEP 2 rng `2`: topic `Pattern formation in reaction-diffusion systems`.
- STEP 3 cold list + STEP 4 rng `5`: NODE `The sensitivity of pattern onset to nondimensionalization choices and hidden parameter scalings`.
- Standing-order target pick: file rng `2` -> `docs/consolidated/01-landscape-and-geometry.md`; topic rng `13` -> off-line FE-quartet convex window.
- STEP 5 constraint: onset statements can be wrong if the hidden length/time scale is not nondimensionalized correctly.
- STEP 8 selected transfer by Levenshtein: `raw curvature thresholds hide the quartet scale a` (`67`).
- STEP 9 method rng `10` = test extreme cases.
- STEP 11 method rng `2` = attack as false.

## Computation
Archive script: `computations/2026-06-21-penrose-r56-curvature-hidden-scaling.py`.

Source NODE validation used a Swift-Hohenberg-style onset toy:
- physical `L=9.70`, `q0=2.00`: selected mode `n*=3`, `mu_c=0.050072`;
- wrong nondimensionalization `L'=1`, `q0'=q0`: selected mode `n*=1`, `mu_c'=1258.718116`;
- correct nondimensionalization `L'=1`, `q0'=q0 L`: selected mode `n*=3`.

Target test used the off-line quartet curvature kernel
`C_a(tau)=2(a^2-tau^2)/(a^2+tau^2)^2`.

With fixed raw grid `h=1`, detection of the positive core obeyed the hidden scale parameter `a/h`:
- `a/h=0.010`: detected `0.0202`, theory `0.0200`;
- `a/h=0.100`: detected `0.2029`, theory `0.2000`;
- `a/h=0.500`: detected `1.0000`, theory `1.0000`.

Holding the dimensionless grid `q=h/a` fixed made scaled hit sizes invariant across `a`:
- `q=0.25`: `a^2 max C` = `1.96926` for all tested `a`;
- `q=0.50`: `1.88147` for all tested `a`;
- `q=1.00`: `1.60083` for all tested `a`;
- `q=2.50`: detection `0.7990`, `a^2 max C=0.99585` for all tested `a`.

## Attack-as-false
The formula is not false: `a^2 C_a(a x)=2(1-x^2)/(1+x^2)^2`, and sampling detection is controlled by `q=h/a`.

The novelty claim is false. R36 already banked the sign-changing off-line curvature kernel and broad-filter erasure; R37 banked the matched localization width near `a/2`; R53 banked grid-stability requirements. R56 is another expression of the same scale passport and sampling certificate.

## Reading
A correct off-line curvature detector must report its dimensionless sampling/localization scale relative to `a=|beta-1/2|`. This is useful instrumentation, but it does not add a new invariant or theorem.
