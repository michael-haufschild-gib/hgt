# Finite consequences of the certified arithmetic inputs

- **ID:** review-1411-finite-work-obstacles
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1411/obstacles-summary.md`, §2.1.

## Required theorems

| Task | Exact scope | Status |
|---|---|---|
| A1 | Jensen real-rootedness for every degree at most `31922`, from width `3/8` and verified height `67`. | Width checked; Jensen check pending |
| A2 | Common certified floor interfaces for smaller apertures, real/complex tests, step packets, charge-free neutral forms and dressed middles; constants and cutoff ranges explicit. | Lean draft; check pending |
| A3 | Exact rational ladder milestones and decomposition of `levelAt 2 4` into its three remaining nonnegative excesses. | Lean draft; check pending |
| A4 | Actual pole/Gamma/jump/root-number terms in WL, CHMD, SZ, HAT-C and PM transfers. | WL/CHMD/SZ/HAT-C drafts; PM pending |
| A5 | The `2^ρ/3^ρ` trace equation, two/three reflection discriminants, double-collision sheet exchange and contact ideals at degrees `1,2,3,4,9`. | Lean drafts; checks pending |
| A6 | Primitive completion and scattering for the actual third-cyclotomic Eisenstein family. | Sources located; specialization pending |
| A7 | Three-even-moment Gram certificate with exact margin `1/1000000`, and strictness exactly for nonzero moment triples. | Public interface drafted in existing moment module; check pending |

## Mathematical reductions

- `SquareRootThreshold.zetaZeroWidth_le_three_eighths`: direct Lean and axiom audit passed
  (`propext`, `Classical.choice`, `Quot.sound`). The sector budget is
  `(d−1)·9/64≤4489`; `31922` satisfies it and `31923` does not.
- The first overlap loss is zero. Monotonicity and nonnegativity of `levelAt` make
  `levelAt Q 4=0` equivalent to three zero-level excesses at ratios
  `10609/5000`, `112550881/50000000`, and `103^8/(100^8/2)`, for `Q≥2`.
- The two prime reflection differences have product in the zero's pair field.
  Its square is `(T₂²−8)(T₃²−12)`. The two differences cannot both vanish,
  by injectivity of the two prime exponent coordinates and nonrealness of every ξ zero.
- Scattering normalization transfers the certified floor only with jump tail,
  Robin mass correction and omitted prime contacts all retained.

## Boundaries

No all-aperture positivity, vanishing of the remaining overlap excesses, collision existence,
Artin holomorphy, infinite square-class classification or improved scattering rate is asserted.
Domain restrictions on tests and finite windows must remain explicit; no unproved analytic
premise may replace an actual input. Each delivered endpoint requires a direct Lean check,
transitive axiom audit and owning umbrella import.
