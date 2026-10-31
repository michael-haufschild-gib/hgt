# Size-only repair reaches the Weyl floor 2/3

- **ID:** size-repair-weyl-floor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #16; `reboot-final.md` WP-B1/B3
- **Statement:** For every `ε > 0` there is `t₀` such that for `|t| ≥ t₀`, every heat
  `λ ≥ (2/3 + ε)/log |t|` and every `m`, `T_{2m}(λ, 0, t) > 0`; with explicit constants at rate
  `67/100`. Hence `limsup λ_t log |t| ≤ 2/3`.

## Lean
Module `RHTower/Heat/SizeOnlyRepairNearTheWeylFloor.lean` (namespace `RHTower`, final theorems in
`RHTower.DeBruijn`): `mul_le_sum_three`, `exists_norm_xiSliceProduct_le_three_profiles`,
`exists_norm_iteratedDeriv_xiSliceProduct_le_inner_three_profiles`, `weylFloorRateTwo`,
`xiSliceReal_mul_gauss_ge_window_width`, `weylFloor_gap_pos_one`, `_two`, `_three`,
`sq_min_hundredth_le`, `weylFloor_gaps_of_eps`, `exists_xiSliceHeatTransfer_pos_low_order_weylFloor`
(parameters `η ≤ 1/12`, window `ω ≤ 1/100`), `DeBruijn.exists_xiSliceHeatTransfer_pos_at_heat_of_low_order`,
`DeBruijn.exists_xiSliceHeatTransfer_pos_heat_of_at_heat`,
`DeBruijn.exists_xiSliceHeatTransfer_pos_heat_weylFloor` (`67/100`),
`DeBruijn.exists_xiSliceHeatTransfer_pos_heat_two_thirds_add` (every `ε > 0`). `TheLocalHeatThreshold`:
`exists_localHeatThreshold_mul_log_le` and `exists_heat_pincer` at `67/100`,
`exists_localHeatThreshold_mul_log_le_two_thirds_add` at `2/3 + ε`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
The proof of `exists_xiSliceHeatTransfer_pos_heat_interior` with a third size piece. With
`μ(½) ≤ 1/6`, `μ(11/18) ≤ 1/9` (corpus `ZetaElevenEighteenthsProfiles`), `μ(5/7) ≤ 1/14`, the slice
relative profiles are `t^{−1/6}` for `|a| ≤ 1/9` (flat: `2(1/6 + η − |a|/2) − (½ + 2η − |a|) = −1/6`),
`t^{−(1/13 + (3/13)(½ − |a|))}` for `1/9 ≤ |a| ≤ 3/14`, and the corpus outer piece. The Cauchy circle of
radius `N/(u + 2E)` carries each profile into an inner exponent `bᵢ = pᵢ + sᵢ/2 − sᵢ²κ/2`:
`b₁ = 1/6`, `b₂ = 5/26 − 9κ/338`, `b₃ = η + c₂/2 − c₂²κ/2`. Window exponent
`a = κ/2 − ½ − 2η − 1/12000`. At `η = 1/2000`, `κ = 67/100`: `a + b₁ ≈ 5.8·10⁻⁴`, `a + b₂ ≈ 8.4·10⁻³`,
`a + b₃ ≈ 2.3·10⁻⁴`, all positive. With window width `ω` the window loss is `5ω²/6`; at
`κ = 2/3 + ε`, `η = ε/16`, `ω = min(1/100, ε)` the gaps are `3ε/8 − 5ω²/6`,
`4/507 + (80/169 − 1/8)ε − 5ω²/6`, and `ε/8 + P(ε)/(2(2/7 + ε/16)²) − 5ω²/6` with
`P(ε) = (51/2352)ε + (29/896)ε² − (3/2048)ε³ > 0`; `5ω²/6 ≤ ε/120`. Orders above `log t` are positive by
the quarter-log coefficient theorem; order `0` by positivity of the slice.

## What it changes (WP-B1, B3)
Frontier number: `κ_repair` from `17/25 = 0.68` to `2/3 + ε` for every `ε > 0`. The Weyl bump
(`a-weyl-bump-breaks-size-only-repair.md`) shows no size-only argument goes below `2/3`: the size-only
repair rate is exactly `2/3 = 4μ(½)`, the Weyl exponent at the centre. The signed bump (`a-signed-weyl-bump-attains-the-method-floor.md`)
showed that `27/40` was the exact floor of the two-piece inputs. The gain comes from flattening the
centre of the profile (slope `0`), not from real-axis positivity. As `η → 0` with a shrinking window,
The corpus already reached `2/3` for the de Bruijn reality
horizon with the same three pieces (`KiKimLeeTwoThirdsHorizon`); this module carries it to the slice.

## Log
- 2026-10-31 — created; proved; formalized.
