# The local heat threshold is depth squared over the local count

- **ID:** local-heat-threshold
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #6
- **Statement:** For `λ_t = inf{λ ≥ 0 : every T_n(λ, 0, t) ≥ 0}`: `λ_WD = sup_t λ_t`; a zero `ρ` with
  `Re ρ > ½`, `Im ρ = t ≥ e^{1600}` gives `λ_t ≥ (Re ρ − ½)²/(200 log t)`; if `Ξ(t) ≠ 0`, the zeros with
  `|Im ρ − t| < ½` have depth `≤ δ`, `R ≥ 0`, `R² ≥ 2δ²` and `N(t, R) ≥ 1`, then
  `λ_t ≤ 64R²/N(t, R)`; if moreover no copy lies within `√2δ`, then `λ_t = 0`.

## Lean
Module `RHTower/Heat/TheLocalHeatThreshold.lean` (namespace `RHTower.DeBruijn`): `localHeatThreshold`,
`localHeatThreshold_le_wdHeatThreshold`, `wdHeatThreshold_eq_iSup_localHeatThreshold`,
`le_localHeatThreshold_of_offLine_zero`,
`localHeatThreshold_le_of_depth_count`, `localHeatThreshold_eq_zero_of_depth`,
`localHeatThreshold_pos_of_re_xiSliceCoeff_neg`, `localHeatThreshold_pos_iff` (`λ_t > 0` iff some
unheated slice coefficient at `t` is negative), `exists_re_xiSliceCoeff_neg_of_offLine_zero`,
`localHeatThreshold_pos_of_offLine_zero` (`λ_{Im ρ} > 0` at every off-line ordinate, every height),
`eventually_volume_localHeatThreshold_eq_zero_ge` (`λ_t = 0` on lower density `29/50`),
`eventually_volume_localHeatThreshold_gt_le` (for every `κ > 0`, `vol{t ∈ [U/4+2, U/2−2] : λ_t > κ/log U} ≤ εU`
eventually: the local rate vanishes in density), `lowerSemicontinuous_localHeatThreshold`,
`isOpen_setOf_localHeatThreshold_pos`,
`riemannHypothesis_iff_volume_setOf_localHeatThreshold_pos_eq_zero` (RH iff `vol{λ_t > 0} = 0`),
`localHeatThreshold_le_of_cone` (`λ_t ≤ λ` when every zero has `(Im z)² ≤ (Re z − t)² + 3λ`),
`exists_inside_cone_of_localHeatThreshold_pos` (`λ_t > 0` forces a zero with `|Re z − t| < |Im z|`),
`exists_localHeatThreshold_mul_log_le` (`λ_t log t ≤ 67/100`),
`exists_localHeatThreshold_mul_log_le_two_thirds_add` (`≤ 2/3 + ε`), `exists_heat_pincer`
(`(Re ρ − ½)²/200 ≤ λ_{Im ρ} log Im ρ ≤ 67/100`), `le_localHeatThreshold_of_zeroGrowth`,
`le_newmanConstant_of_zeroGrowth` (linear lower bound
`δ/(3000(b + c + 1) log t)` for `λ_t` and `Λ` when `Ψ_{t,r}` is regular). Axioms: `propext`,
`Classical.choice`, `Quot.sound`.

## Paper proof
Support: off-line ordinates `⊆ {λ_t > 0} ⊆` the heated shadow `⋃_z {|Re z − t| < |Im z|}`. At an
ordinate the slice vanishes at `x = δ > 0`, so some unheated coefficient is negative (a nonnegative
series vanishing at `δ` is zero, but the slice is not); `T_n(λ, 0, t)` is continuous in `λ`. Off the
shadow the heated cone criterion holds at `λ = 0`. Openness: a heat `λ₁ < λ_t` fails at `t` in some
order, `Re T_n(λ₁, 0, ·) < 0` is open in the height, and positivity is closed upward in `λ`; an open
null set is empty, and then `λ_WD = sup_t λ_t = 0`.

Positivity is closed upward in `λ` (`xiSliceHeatTransfer_nonneg_of_le_of_forall`), so `λ_t` is a
threshold; `λ > sup_t λ_t` is admissible at every height, so `λ_WD = sup_t λ_t`. Lower bound: below the bound, raise `λ` to `max(λ, bound/2)` and apply
`re_xiSliceHeatTransfer_neg_of_slice_zero_quadratic`. Upper bound: `xiSliceHeatTransfer_nonneg_of_depth_count`
at `λ = 64R²/N(t, R)` (`R > 0` because `Ξ(t) ≠ 0` empties the radius-`0` head). Empty head: every
copy is outside the cone (`im_sq_le_of_not_mem_radiusHead_of_depth`), so the heated cone criterion
holds at `λ = 0`.

## What it changes
The heat instrument is one number per height, `λ_t`, pinned between `depth²/(200 log t)` and
`128 depth²/N(t, √2 depth)`. Every-height heat positivity at rate `κ` is the statement
`sup_t λ_t log t ≤ κ`, so heat statements are statements about local depth over local count.

## Log
- 2026-10-31 — created; proved; formalized.
