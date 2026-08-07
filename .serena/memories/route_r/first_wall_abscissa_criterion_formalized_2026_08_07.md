# Route R first wall at the abscissa — FORMALIZED, cone unblocked (2026-08-07)

Completes the arc: `mem:route_r/first_wall_lane_classified_terminus_2026_08_06` →
`mem:route_r/analytic_abscissa_reader_formalized_2026_08_07` →
`mem:route_r/abscissa_reader_effective_bounds_2026_08_07` → this.

## Cone unblocked

`lake build GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion` finally completed
(11303/11303) after six successive `timeout 540`-capped attempts, each making partial progress with no
errors. Repeated capped retries DO converge once the competing full-area builds thin out — the earlier
zero-progress attempt was lock contention at 13 concurrent builds, not a hang.

Both theorems written blind while the cone was down are confirmed, axioms
`[propext, Classical.choice, Quot.sound]`: `primeHarmonicResidueMod_unique`,
`riemannHypothesis_of_frequently_negligible_producer`.

## New module `RHTower/RouteRFirstWallAbscissaCriterion.lean`

`lake build` green (11307 jobs), axioms clean, in the umbrella.

- `tendsto_primeAbscissa_criticalWall_{neg_one_of_pos, one_of_neg}` — the analytic three-value law,
  each a ONE-LINE instantiation of `tendsto_primeAbscissaSeries_div_abscissaLog` against the corpus
  residue facts `hasReferenceResidue_criticalWall_*`. This is the payoff of having built the reader
  generically and off-cone.
- `primeAbscissaSeries_criticalWall_zero`.
- `eq_zero_of_frequently_abs_re_primeAbscissa_le`.
- `riemannHypothesis_iff_frequently_abs_re_primeAbscissa_lt_one` — RH as an `iff` about the boundary
  behaviour of ONE explicit prime Dirichlet series.

`not_frequently_abs_re_le_of_unit_limit` was generalised from `ℕ`/`atTop` to an arbitrary `NeBot`
filter so the same lemma serves both the sequence criterion and the `𝓝[>]1` criterion; both existing
call sites unified unchanged.

## Standing scope note

This is a change of language, NOT a strengthening. The card addendum proves the analytic reader has
the same resolution as the profile reader under `height u = s-1 ↔ 1/log(depth)`, and the bounded-depth
no-go transfers. The first-wall lane remains classified as a criterion re-encoding; do not read the
new `iff` as progress toward a proof.

Card moved to `docs/drafts/pipeline/3-formalized/harmonic-residue-analytic-abscissa-reader.md`.
