# Rational correlation Grams at one critical multiple

- **ID:** finite-rational-correlation-grams-at-critical-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, A7.
- **Target:** For every finite family of positive rationals, its `ratCorr` Gram
  is an entrywise limit of complete Steklov atomic packet Grams at overlap
  `K·loglog N·(logloglog N)²`, with one fixed `K` for that family. In the
  unit-interval normalization, this is a literal complete-matrix compression
  at overlap `2K·loglog N·(logloglog N)²`.

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

For the unit-interval profile `φ(u)=2·steklovDCProfile(2u−1)`, put
`w=c/N`, `G=∫φ(u/w)²du`, and `v_n=x_n/w`. The profile has integral one
and positive square integral, so `G>0`. Recentering and translation invariance
give the exact energy identity `G⟨A_N(c)v,v⟩=W(f_x,f_x)`. Real polarization
gives every mixed entry `G⟨A_N(c)v_i,v_j⟩=W(f_i,f_j)`. At
`c=2K·dcScale N`, the recentred dilation is precisely `N/(K·dcScale N)`.
Thus the same limit is a compression of the normalized complete matrix.

Corpus inputs: `dotProduct_weilGram_eq_ratCorr`,
`tendsto_weilGram_of_perturbation`, `mollify_perturbation`,
`exists_dcLogSynthesis`, and the bounded-rate synthesis estimates in
`ABoundedOverlapRateSeesASemilocalWindow`.

## Lean

`TransMetzlerWeilPositivity/ReceiverRate/ABoundedOverlapRateSeesASemilocalWindow.lean`:

- `exists_dcLogSynthesis_family_gram_limit_of_rate`: simultaneous smooth-family synthesis.
- `eventually_exists_family_gram_approximation_of_rate`: finite C² families, by mollification.
- `exists_ratCorr_gram_approximation_at_critical_multiple`: rational translates at a fixed multiple.
- `exists_ratCorr_gram_limit_at_critical_multiple`: diagonal limit with horizons tending to infinity.
- `completePacketVector_gram`: exact mixed-entry normalization by the positive atom mass.
- `exists_ratCorr_completeWeil_gram_limit`: literal complete-matrix compression limit.

The form is the full Weil Gram, including prime, Gamma, and pole terms.
Atoms use `dilate (N/(K*dcScale N)) steklovDCProfile`; this fixes their
normalization directly. The multiple depends on the finite family; no single
universal multiple or exact pole-moment preservation is asserted.

Direct leaf audit passed. All six declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Existing umbrella import includes the leaf.
