# The off-line second moment is o(V)

- **ID:** off-line-second-moment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #36
- **Statement:** `Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½)₊² = o(V)`, unconditionally. Consequence: for every
  `W > 0` and `ε > 0`, for large `T`, the centres `S ∈ [T − 1, 2T + 1]` whose window `(S − 1, S + 1]`
  has right-half depth mass `Σ_{Re ρ > ½} m (Re ρ − ½)² > W` have measure `≤ εT`. Deep zeros: for every
  `d₀ > 0`, `#{Re ρ ≥ ½ + d₀, 0 < Im ρ ≤ V} = o(V)`, and the centres `S ∈ [T − 1, 2T + 1]` with a zero of
  depth `≥ d₀` at `|Im ρ − S| ≤ 1` have measure `≤ εT` for large `T`.

## Lean
Module `SquareRootThreshold/TheOffLineSecondMomentIsLittleO.lean` (namespace `RHTower`):
`offLineSecondMoment`, `offLineSecondMoment_nonneg`, `sq_max_le_half_tail_add`,
`offLineTail_zero_le_offLineMoment`, `tendsto_offLineSecondMoment_div`, `tendsto_offLineCountBeyond_div`,
`volume_deepWindow_le`, `eventually_volume_deepWindow_le`; the depth-mass consequence in
`SquareRootThreshold/TheLocalCountHoldsForAlmostAllHeights.lean` (namespace
`RHTower.LocalCountFalsifier`): `rightDepthMass`, `rightDepthMass_eq_sum`,
`sum_window_le_offLineSecondMoment`, `eventually_volume_rightDepthMass_gt_le`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
For `x ≤ ½` and every `d`: `x₊² ≤ ½(x − d)₊ + d x₊`. Below `0` both sides vanish or are positive; on
`(0, d]` use `x ≤ d`; above `d`, `x(x − d) ≤ ½(x − d)`. Summing over the zeros with `x = Re ρ − ½`:
`Σ m x₊² ≤ ½ offLineTail(d, V) + d offLineTail(0, V)`. With `d = R/log V`, Selberg's tail law
(`eventually_offLineTail_le_selberg`) gives `4π offLineTail(R/log V, V) ≤ (g(R) + η)V`,
`g(R) = −log(1 − e^{−2R/15}) → 0`. The zero-shift tail is the off-line first moment, `≤ (67/1000) V`, so
`d offLineTail(0, V) = O(RV/log V)`. For `ε > 0` pick `R` with `g(R) < ε` and `η = ε`; then
`Σ m x₊² ≤ ε V/2` for large `V`. Consequence: the depth mass of the window about `S` is a sum of
indicators of `[Im ρ − 1, Im ρ + 1)`, so its integral over `S ∈ [T − 1, 2T + 1]` is at most twice the
window's second-moment sum, `≤ 2 offLineSecondMoment(2T + 2)`; Markov at level `W` gives measure
`≤ 2δ(2T + 2)/W ≤ εT` with `δ = εW/8`. Deep zeros: `(d₀/2) #{Re ρ ≥ ½ + d₀} ≤ offLineTail(d₀/2, V)
≤ offLineTail(R/log V, V)` once `R/log V ≤ d₀/2` (`offLineTail_anti`), and the Selberg tail law gives
`≤ εd₀V/4` for `g(R) < εd₀/2`. A deep zero (or its reflection, same ordinate) covers centres in
`[Im ρ − 1, Im ρ + 1]`, so the deep windows have measure `≤ 2 #{deep zeros up to 2T + 2} = o(T)`.

## What it changes (A2, CCM)
The off-line first moment `≍ V` sits at depths `o(1)`: the depth mass `Σ m (Re ρ − ½)²` of a unit window
is `o(1)` on average over heights, and its right half is `≤ W` off a set of window centres of density
`o(1)`, for every `W > 0`. That is the depth-weighted local input of the CCM ground-energy floor
(`OffLineDepthLocallyBounded W`; its left half mirrors the right by `ρ ↦ 1 − ρ̄`). Its pointwise form fails under counting (#34). The count input (bounded off-line copies
per window) instead forces critical proportion one even in density (#33, #35). So the depth-weighted
input is the right one: true on average, missing pointwise. Likewise the deep-companion input of the
lag family (companions of depth `≥ 3δ₀/8` near the record) holds with no companion at all for
almost all heights; only its pointwise form is missing.

## Log
- 2026-10-31 — created; proved; formalized.
