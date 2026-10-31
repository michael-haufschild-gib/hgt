# Heat repair from the local depth and the local count

- **ID:** heat-repair-depth-count
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #3; `reboot-final.md` WP-B2
- **Statement:** Let `Ξ(t) ≠ 0`, `λ > 0`, and let every zero `ρ` with `|Im ρ − t| < ½` have
  `|Re ρ − ½| ≤ δ`. If `R ≥ 0`, `R² ≥ 2δ²` and `64R² ≤ λ N(t, R)` (`N(t, R)` = zero copies within
  distance `R` of `½ + it`), then every `T_n(λ, 0, t) ≥ 0`.

## Lean
Module `RHTower/Heat/HeatRepairFromLocalDepthAndCount.lean` (namespace `RHTower.DeBruijn`):
`xiSliceHeatTransfer_nonneg_of_depth_count` (main), `xiSliceHeatTransfer_nonneg_of_depth_of_card_pos`
(`λ ≥ 128δ²` once the radius-`√2δ` head is nonempty), `im_sq_le_of_not_mem_radiusHead_of_depth`,
`coeffNonneg_forwardPolyHeat_sliceTruncPoly_sdiff_of_depth`. Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

## Paper proof
Slice = head (copies within `R`) × tail. Head: `N(t,R)` roots in `|x²| ≤ R²`, repaired at heat
`λ/2 ≥ 32R²/N(t,R)` (`coeffNonneg_heat_sliceTruncPoly_radiusHead`). Tail copy `z`: if
`|Re z − t| ≥ ½` then `(Im z)² < ¼ ≤ (Re z − t)²`; otherwise `(Im z)² ≤ δ²` and
`(Re z − t)² > R² − (Im z)² ≥ δ²`. Either way the pair factor is outside the cone and heat-positive
(`coeffNonneg_forwardPolyHeat_slicePair`); heat positivity is closed under products; the finite
truncations converge to the slice coefficients (`tendsto_coeff_forwardPolyHeat_sliceTruncPoly`).

## What it changes
The local heat threshold at height `t` is `depth²/local count` on both sides:
- repair: `λ ≤ 128δ²/N(t, √2δ)` (this card);
- detection: `λ ≥ δ²/(200 log t)` for a zero of depth `δ` at height `t`
  (`heat-detection-rate-is-quadratic-in-the-depth.md`), sharp for central clusters
  (`a-central-cluster-hides-an-off-line-zero-from-heat.md`).
For mean density `N(t, √2δ) ≍ δ log t` both ends are `≍ δ/log t`; for a cluster `N ≍ log t` both are
`≍ δ²/log t`. Heat positivity at rate `κ` is therefore equivalent, up to constants, to a bound on
`depth² × log t/local count` at every height: it carries exactly the information of the local
zero geometry and no more. Closing the heat pincer (WP-B) is the same problem as bounding depths.

## Log
- 2026-10-30 — created; proved; formalized.
