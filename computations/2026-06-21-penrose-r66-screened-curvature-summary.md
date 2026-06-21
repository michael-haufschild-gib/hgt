# R66 — screened off-line curvature

**Verdict:** DEAD END / overlaps existing localization passport.

## Setup
- Seed RandomNode: `Local detailed-balance constraints on transition rates in stochastic assembly models`.
- STEP 1 cold list + STEP 2 rng `19`: topic `Topological defects in active matter`.
- STEP 3 cold list + STEP 4 rng `7`: NODE `The role of substrate friction in screening hydrodynamic interactions between defects`.
- Standing-order target pick: file rng `2` -> `docs/consolidated/01-landscape-and-geometry.md`; topic rng `23` -> positivity/localization axis.
- STEP 5 constraint: screening suppresses long-range interactions and changes what local defect signal remains visible.
- STEP 8 selected transfer by Levenshtein: `positivity localization depends on screening length relative to defect width` (`61`).
- STEP 9 method rng `15` = strengthen.
- STEP 11 method rng `10` = test extreme cases.

## Computation
Archive script: `computations/2026-06-21-penrose-r66-screened-curvature.py`.

The target test integrated the off-line quartet curvature kernel
`C_a(tau)=2(a^2-tau^2)/(a^2+tau^2)^2`
against exponential screening `exp(-|tau|/lambda)`.

Scale-collapsed screened mass:

| lambda/a | a * screened_mass |
|---:|---:|
| 0.10 | 0.37954304 |
| 0.20 | 0.67792515 |
| 0.50 | 1.15636272 |
| 1.00 | 1.37351199 |
| 2.00 | 1.34538388 |
| 5.00 | 1.03508414 |
| 10.00 | 0.74643205 |
| 50.00 | 0.26922775 |

The same values held for `a=0.1` and `a=0.2`, confirming the dimensionless scale `lambda/a`. The unscreened whole-line mass is analytically zero because the kernel has zero signed area.

## Extreme Cases
- Very short screening sees too little of the core.
- Screening near `lambda ~ a` best suppresses negative wings while retaining the positive core.
- Very long screening tends back toward the zero-area unscreened kernel.

## Reading
This is a useful exponential-screening detector family for the positivity/localization axis, but it is not independent of the existing off-line curvature localization passport and matched-width results.
