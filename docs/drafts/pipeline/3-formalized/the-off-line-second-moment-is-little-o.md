# The off-line second moment is o(V)

- **ID:** off-line-second-moment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #36
- **Statement:** `Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½)₊² = o(V)`, unconditionally.

## Lean
Module `SquareRootThreshold/TheOffLineSecondMomentIsLittleO.lean` (namespace `RHTower`):
`offLineSecondMoment`, `offLineSecondMoment_nonneg`, `sq_max_le_half_tail_add`,
`offLineTail_zero_le_offLineMoment`, `tendsto_offLineSecondMoment_div`.
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
`Σ m x₊² ≤ ε V/2` for large `V`.

## What it changes (A2, CCM)
The off-line first moment `≍ V` sits at depths `o(1)`: the depth mass `Σ m (Re ρ − ½)²` of a unit window
is `o(1)` on average over heights. So the depth-weighted local input of the CCM ground-energy floor
(`OffLineDepthLocallyBounded W`) holds with every `W > 0` off a set of window centres of density
`o(1)` (Markov). Its pointwise form fails under counting (#34). The count input (bounded off-line copies
per window) instead forces critical proportion one even in density (#33, #35). So the depth-weighted
input is the right one: true on average, missing pointwise.

## Log
- 2026-10-31 — created; proved; formalized.
