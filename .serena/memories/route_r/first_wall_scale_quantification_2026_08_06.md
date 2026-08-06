# Route R first wall is a scale detector (2026-08-06, second pass)

Builds on `mem:route_r/harmonic_quantum_gap_criterion_2026_08_06`. All unconditional, axioms
`[propext, Classical.choice, Quot.sound]`.

## New single-stage API in `HTGeometry/CofinalUnitProfileResidue.lean`

- `IsUnitStage h w` — the honest per-stage hypothesis: `0 ≤ w ≤ 1` and `HasSum (w * h) 1`. Escape of
  supports is a property of the *family*, not of a stage. `IsCofinalUnitProfile.isUnitStage` projects.
- `stageAverage w a = ∑' i, (w i : ℂ) * a i`; `profileAverage mu N = stageAverage (mu N)` by `rfl`
  (`profileAverage_eq_stageAverage`).
- `tsum_stageWeighted_le` / `le_tsum_stageWeighted` — compare a stage average against the unit
  reference mass termwise. These are the engine of every depth estimate: state the hypothesis
  multiplicatively as `w i * d i ≤ K * (w i * h i)` so the `w i = 0` case is free.
- `norm_stageAverage_ofReal` — modulus of a real-valued stage average is `|∑' w f|`.

## `RHTower/RouteRFirstWallScaleQuantification.lean`

Exact modulus identity, sign-free: `abs_criticalWallCoefficient_eq` gives
`|W_t(p)| = F(p) * (1 - p^(-2|t|))` with `F = primeActivationOccupancyFisherDensity = p/(p+1)^2`,
covering `t>0`, `t<0` and `t=0` (both sides vanish at `t=0`).

**Depth lower bound** `le_norm_stageAverage_criticalWall`: for a stage carried by primes `≥ q ≥ 3`,

  `(1 - q^(-2|t|)) * (1 - 3/q) ≤ ‖stageAverage w (W_t)‖`.

Two ingredients: `1 - p^(-2|t|) ≥ 1 - q^(-2|t|)` (`Real.rpow_le_rpow_of_nonpos`), and
`F(p) ≥ (1 - 3/q)/p` from the corpus bound `1/p - F(p) ≤ 3/p²` together with `q ≤ p`.

**Explicit grade bound** `abs_le_of_norm_stageAverage_le`: with `q ≥ 4` and `r < 1 - 3/q`,
a stage modulus `≤ r` forces `|t| ≤ log((1-3/q)/(1-3/q-r)) / (2 log q)`.

**Deep-stage criterion** `eq_zero_of_deepStage_norm_profileAverage_le`: arbitrarily deep stages with
one common `r < 1` force `t = 0`. The stage index is unconstrained — only prime depth enters.

## Sharpened asymptotic criterion (same file family, gap-criterion module)

`eq_zero_of_frequently_abs_re_profileAverage_le` and
`riemannHypothesis_of_frequently_abs_re_profileAverage_lt_one`: only the **real part** and only
**frequently** (`∃ᶠ`) is needed, since the limit is real of modulus 0 or 1.

## What the lower bound rules out

The stage average depends on the grade only through `t · log q`, up to `O(1/q)`. So no choice of
weights makes it small by size when `|t| ≫ 1/log q`. A producer must supply genuine cancellation at
one finite explicit depth — that is the whole remaining content
(`ROUTE_R_FIRST_WALL_FINITE_DEPTH_CANCELLATION` in the parent card).

## Lean gotchas hit

- `Summable.norm` lives in `Mathlib/Analysis/Normed/Module/FiniteDimension.lean` and needs
  `FiniteDimensional ℝ ℂ`; import `Mathlib.LinearAlgebra.Complex.FiniteDimensional` too.
- `tendsto_tsum_compl_atTop_zero` is root-namespace and needs no summability.
- `hasSum_sum_of_ne_finset_zero` leaves the `SummationFilter` a metavariable — pin the expected type.
- `Complex.hasSum_ofReal` replaces `Complex.ofRealCLM.hasSum` when the finite-dimensionality
  instance is not imported.
- Dot notation on a `def ... : Prop := Summable …` resolves to the *enclosing* theorem, not to
  `Summable`; write `Summable.add ha hb` explicitly inside `HasReferenceResidue.add`.
