# Analytic abscissa reader — paper-proved, formalization pending (2026-08-06, sixth pass)

Card: `docs/drafts/pipeline/2-fully-proven/harmonic-residue-analytic-abscissa-reader.md`.
Follows `mem:route_r/first_wall_lane_classified_terminus_2026_08_06` — the profile reader is at its
terminus, so this changes *language*, not device.

## The law (paper-proved, dependency-closed)

For `h(p)=1/p`, `a - c·h` summable, and real `s > 1`, put `A(s) = ∑_p a(p) p^{-(s-1)}` and
`L(s) = -log(s-1)`. Then `A(s) = c·P(s) + B(s)` with `|B(s)| ≤ ∑_p |a-c h|` uniformly for `s ≥ 1`
(because `p^{-(s-1)} ≤ 1`), so

  `A(s) / L(s) → c`  as `s → 1⁺`.

So the harmonic residue has TWO unrelated formulas: the cofinal profile average, and the
`log(1/(s-1))`-normalised prime Dirichlet series at the abscissa. The analytic one also reproves the
oriented three-value law in a few lines: with `F(p)=p/(p+1)²`, `Φ(s)=∑_p F(p)p^{-(s-1)} = P(s)+O(1)`
and `Φ(s+2|t|) ≤ P(1+2|t|) < ∞`, hence `∑_p W_t(p)p^{-(s-1)} = -sign(t)·P(s)+O(1)`.

## Corpus input — do not re-derive

`RHTower/PrimeZetaLogAsymptotic.lean` (added by another session on 2026-08-06) already has
`primeZeta s = ∑' p, p^(-s)`, `primeLogDefect`, and

  `tendsto_primeZeta_add_log_sub : Tendsto (fun s => primeZeta s + Real.log (s-1)) (𝓝[>] 1)
     (𝓝 (-primeLogDefect 1))`.

That is the only analytic input needed. NOTE: at the time of writing this module was not yet in the
`RHTower` umbrella (lint flagged it unreachable) — importing it directly is still fine.

## Planned Lean layer (next step)

Target `RHTower/HarmonicResidueAbscissaReader.lean`: `primeAbscissaSeries`, `abscissaLog`,
summability from `HasReferenceResidue`, the split `A = c·P + B`, the uniform bound on `B`, the three
scalar cores (see below), then the reader law, the analytic three-value law, and the analytic RH
characterization matching
`riemannHypothesis_iff_frequently_abs_re_profileAverage_lt_one`.

Scalar cores drafted (unverified — see contention note): `-log(s-1) → atTop` on `𝓝[>]1` via
`Real.tendsto_log_nhdsGT_zero` composed with `s ↦ s-1` and `tendsto_neg_atBot_iff`; bounded/atTop → 0
via `squeeze_zero_norm'` + `Tendsto.div_atTop`; and `P/L → 1` from `(P-L) → k` plus
`Tendsto.div_atTop`.

## Contention note (2026-08-06 ~23:40)

Twelve concurrent `lake build GaloisForLFunctions*` processes across several Claude sessions plus a
Codex session (that one on `/tmp/route_r_bounded_covariance_scratch.lean`). A full-area RHTower
rebuild was in flight, so project-module oleans were transiently absent and even a Mathlib-only
`lake env lean` did not finish inside ten minutes. Nothing was built or verified in this pass by
design. Two theorems from the previous pass remain unverified:
`primeHarmonicResidueMod_unique` and `riemannHypothesis_of_frequently_negligible_producer` in
`RHTower/RouteRHarmonicQuantumGapCriterion.lean` — everything before them in that file passed
`lake env lean` cleanly.
