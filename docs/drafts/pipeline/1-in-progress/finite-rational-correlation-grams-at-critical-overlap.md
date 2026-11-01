# Rational correlation Grams at one critical multiple

- **ID:** finite-rational-correlation-grams-at-critical-overlap
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, A7.
- **Target:** For every finite family of positive rationals, its `ratCorr` Gram
  is an entrywise limit of complete Steklov atomic packet Grams at overlap
  `K·loglog N·(logloglog N)²`, with one fixed `K` for that family.

## Proof route

Write the rational Gram as the Weil Gram of translates of the cubic spline.
Choose common support radius `R`, sup bound `M`, and Lipschitz bound `L`.
Mollification by the Steklov profile converges in the sup and Lévy norms,
hence jointly in every entry of the finite Gram.

At each fixed mollifier width, bounded-rate Euler–Maclaurin synthesis has
vanishing sup and Lévy errors whenever
`K>288e·blockSize(R+1)`. This condition depends on support, not on the
mollifier width. For each entry tolerance, first fix a sufficiently narrow
mollifier and then a sufficiently large horizon. A diagonal choice gives
the asserted Gram limit along horizons `N=n·blockSize(R+1)`.

Corpus inputs: `dotProduct_weilGram_eq_ratCorr`,
`tendsto_weilGram_of_perturbation`, `mollify_perturbation`,
`exists_dcLogSynthesis`, and the bounded-rate synthesis estimates in
`ABoundedOverlapRateSeesASemilocalWindow`.

## Remaining proof obligations

- Joint finite-family synthesis with one horizon and one translation.
- Exact packet-to-complete-matrix normalization.
- Concrete Steklov specialization, direct Lean and axiom audits.
