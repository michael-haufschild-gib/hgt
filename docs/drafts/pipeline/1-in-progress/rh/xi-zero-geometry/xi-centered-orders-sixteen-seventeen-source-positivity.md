# Xi centered orders sixteen and seventeen source positivity

- **ID:** xi-centered-orders-sixteen-seventeen-source-positivity
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** centered order-fifteen corner method plus existing order-sixteen and
  order-seventeen sector lemmas
- **Statement:** Centered reciprocal-square Xi atoms have positive real powers sixteen and
  seventeen; hence normalized prime--archimedean moments fifteen and sixteen are positive.

## Goal

Extend unconditional source-moment positivity through index sixteen and discharge the
prime--Gamma Hankel condition for every degree-at-most-eight polynomial whose real square has
nonnegative coefficients.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and rational corner attack
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, exact-file check, axiom audit, umbrella build
- [ ] 3 → 4 publication-ready: post-proof collision audit

## Corpus inputs

- `orderSixteenReciprocalPower_re_pos_of_sectorRatio`
- `orderSeventeenReciprocalPower_re_pos_of_sectorRatio`
- `xiZeroCopy_offLine_eightyFive_lt_im_sq`
- `xiFourthReciprocalTraceAtom_nonneg`
- FE--Schwarz fourth-trace invariance
- `normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand`

## Approach

For `u = (Re rho - 1/2)^2`, `v = (Im rho)^2`, `A=v-u`, and `B^2=4uv`:

- order sixteen: failure of `104 B^2 < A^2` lies in
  `1/6 < u < 1/4`, `85 < v < 105`;
- order seventeen: failure of `118 B^2 < A^2` lies in
  `1/6 < u < 1/4`, `85 < v < 119`.

On both corners prove the fourth reciprocal-trace atom exceeds `1/20000`. Four FE--Schwarz
copies then contradict the complete source upper bound `9/50000`. Apply the existing complex
sector lemmas and sum absolutely.

## Log

- 2026-07-25 — created after centered power-fifteen closure.
- 2026-07-25 — exact rational proof completed and checked in
  `RHTower/XiCenteredOrdersFifteenSixteenSourcePositivity.lean`; moments fifteen/sixteen feed the
  full degree-eight square-coefficient cone and remove a concrete monic two-Eisenstein degree-eight
  test from combined Sonin residual.
- 2026-07-25 — post-proof literature search found related superzeta/secondary-zeta and Li-criterion
  reciprocal-power work, but no exact unconditional centered power-sixteen/seventeen sign theorem;
  no priority claim made.
