# Finite consequences of the certified arithmetic inputs

- **ID:** review-1411-finite-work-obstacles
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1411/obstacles-summary.md`, §2.1.

## Required theorems

| Task | Exact scope | Status |
|---|---|---|
| A1 | Jensen real-rootedness for every degree at most `31922`, from width `3/8` and verified height `67`. | Direct Lean and axiom audits passed |
| A2 | Common certified floor interfaces for smaller apertures, real/complex tests, step packets, charge-free neutral forms and dressed middles; constants and cutoff ranges explicit. | Lean draft; check pending |
| A3 | Exact rational ladder milestones and decomposition of `levelAt 2 4` into its three remaining nonnegative excesses. | Lean draft; check pending |
| A4 | Actual pole/Gamma/jump/root-number terms in WL, CHMD, SZ, HAT-C and PM transfers. | Lean drafts; checks pending |
| A5 | The `2^ρ/3^ρ` trace equation, two/three reflection discriminants, double-collision sheet exchange and contact ideals at degrees `1,2,3,4,9`. | Lean drafts; checks pending |
| A6 | Primitive completion and scattering for the actual third-cyclotomic Eisenstein family. | Lean draft; check pending |
| A7 | Three-even-moment Gram certificate with exact margin `1/1000000`, and strictness exactly for nonzero moment triples. | Public interface drafted in existing moment module; check pending |

## Mathematical reductions

- `SquareRootThreshold.zetaZeroWidth_le_three_eighths`: direct Lean and axiom audit passed
  (`propext`, `Classical.choice`, `Quot.sound`). The sector budget is
  `(d−1)·9/64≤4489`; `31922` satisfies it and `31923` does not.
- The first overlap loss is zero. Monotonicity and nonnegativity of `levelAt` make
  `levelAt Q 4=0` equivalent to three zero-level excesses at ratios
  `10609/5000`, `112550881/50000000`, and `103^8/(100^8/2)`, for `Q≥2`.
- Support inclusion preserves the real and complex floor `1/50000` below
  `1881/5000`. The packet dictionary carries it to windows with
  `5000(R+J)≤10609R`, `R≥1`, `Q≥2`; the dressed-middle ranges are
  `100a≤3R` and `50b≤3(R+a)`.
- The two prime reflection differences have product in the zero's pair field.
  Its square is `(T₂²−8)(T₃²−12)`. The two differences cannot both vanish,
  by injectivity of the two prime exponent coordinates and nonrealness of every ξ zero.
- Scattering normalization transfers the certified floor only with jump tail,
  Robin mass correction and omitted prime contacts all retained.
- The Eisenstein character has root number `+1` and Gamma factor `Γℝ(s+1)`.
  The Bianchi phase at the removable origin is `−1`; the completed quotient
  on the punctured spectral axis retains the polar factor. The pulse rate is `1/16−ε`.
- The three-even-moment certificate retains its exact reflected-pair polynomial
  integrals and inverse mixed charge form. Its margin is
  `10⁻⁶(u²+v²+w²)`, hence strictness holds exactly for nonzero triples.

## Boundaries

No all-aperture positivity, vanishing of the remaining overlap excesses, collision existence,
Artin holomorphy, infinite square-class classification or improved scattering rate is asserted.
Domain restrictions on tests and finite windows must remain explicit; no unproved analytic
premise may replace an actual input. Each delivered endpoint requires a direct Lean check,
transitive axiom audit and owning umbrella import.
