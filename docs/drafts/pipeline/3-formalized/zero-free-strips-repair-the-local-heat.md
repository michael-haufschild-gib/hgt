# Zero-free strips repair the local heat

- **ID:** strip-heat-repair
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); the repair half is a receiver (hypothesis: a zero-free strip)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #39
- **Statement.**
  1. *Strip window count.* There is `C > 0` such that if every zero with `|Im ρ| ≥ T₀` has
     `|Re ρ − ½| ≤ d`, then for every `ℓ ≥ 1` there is `M` with, for all large `T`,
     `ℓA² N(T − D/ℓ, T + D/ℓ) ≥ (E/2) log T − M − d e^{2ℓd} s(ℓ) C log T`
     (`A = ∫Φ`, `E = ∫Φ²`, `D² = 2∫Φ′²/E + 1`, `s(ℓ)` explicit).
  2. *Repair.* If moreover `ℓd ≤ 1` and `d e^{2ℓd} s(ℓ) C ≤ E/4`, then
     `λ_t log t ≤ K/ℓ`, `K = 2048 D²A²/E`, at all large `t` with `Ξ(t) ≠ 0`.
  3. *Equivalence.* `λ_t log t → 0` (i.e. `≤ ε` at all large heights, every `ε > 0`) iff for every
     `d > 0` all zeros of large height lie within `d` of the critical line.

## Lean
Module `SquareRootThreshold/AStripGivesLittlewoodWindows.lean` (namespace `RHTower.Littlewood`):
`abs_exp_sub_one_le_mul_exp`, `norm_paperFT_shift_sub_le`, `paperFT_cb_add_two`, `decayConst`,
`norm_paperFT_cb_le_decay`, `shiftConst`, `norm_paperFT_cb_shift_sub_le`, `gammaOf_sub_eq`,
`errConst`, `norm_wsummand_window_sub_le`, `abs_tsum_psi_sub_integral_le`,
`tsum_psi_zero_le_of_summable`, `exists_analytic_window_bound`, `ZeroFreeStrip`,
`exists_tsum_carrier_density_le`, `stripWeight_le`, `stripConst`, `exists_strip_window_count_bound`.
Module `RHTower/Heat/ZeroFreeStripsRepairTheLocalHeat.lean` (namespace `RHTower.DeBruijn`):
`N_le_card_xiSliceGaussianRadiusHead`, `heatRepairConst`, `stripConst_nonneg`,
`exists_localHeatThreshold_mul_log_le_of_strip`, `localHeatThreshold_mul_log_le_of_punctured`,
`localHeatThreshold_mul_log_le_of_forall_ne_zero`,
`eventually_localHeatThreshold_mul_log_le_of_strips`,
`strips_of_eventually_localHeatThreshold_mul_log_le`,
`eventually_localHeat_le_iff_zeros_tend_to_the_line`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
*Shift bounds.* `F_k = (Φ_ℓ^{(k)})^` with `Φ_ℓ^{(k)}` supported in `[−ℓ, ℓ]`. Decay:
`|F_k(x + iy)| ≤ e^{ℓ|y|} B_k/(1 + |x|)²`, `B_k = 4(‖Φ_ℓ^{(k)}‖₁ + ‖Φ_ℓ^{(k+2)}‖₁)` (corpus
`norm_paperFT_le_decay`). Shift: `F(x + iy) − F(x) = ∫Φ(u)e^{ixu}(e^{−yu} − 1)du` and
`|e^w − 1| ≤ |w|e^{|w|}` give `|F(x + iy) − F(x)| ≤ |y|ℓe^{ℓ|y|}‖Φ‖₁`; for `|x| > 1`,
`F_k = −F_{k+2}/z²` splits the difference into `−(F_{k+2}(z) − F_{k+2}(x))/z²` and
`F_{k+2}(x)(z² − x²)/(z²x²)` with `|z² − x²| ≤ 3|x||y|` (`|y| ≤ 1`). Together, for `|y| ≤ 1`,
`|F_k(x + iy) − F_k(x)| ≤ |y|e^{ℓ|y|}(ℓ + 3)B_k/(1 + |x|)²`.

*Summand of an off-line zero.* For `ρ = ½ + η + iγ`, `x = γ − T`: `γ_ρ − T = x − iη`,
`conj γ_ρ − T = x + iη`, and the explicit-formula summand of the window `Φ_ℓ^{(k)}e^{−iTu}` is
`m F(x − iη) conj F(x + iη)`. Writing `F(a)conj F(b) − |F(x)|² = (F(a) − F(x))conj F(b) +
F(x)conj(F(b) − F(x))` gives `|summand − mψ_k(x)| ≤ m c_k |η|e^{2ℓ|η|}/(1 + |x|)⁴`,
`c_k = 2(ℓ + 3)B_k²`.

*Comparison.* The unconditional explicit formula (`paperInputs_zeta.EF`) gives
`Σ summands = ∫ψ_k(τ − T)ν_X`; summable errors `e_ρ` dominating the differences give summability of
`Σ mψ_k(γ − T)` and `|Σ mψ_k(γ − T) − ∫ψ_kν_X| ≤ Σ e_ρ`.

*Error sum under the strip.* Zeros with `|γ| ≥ T₀` have `|η| ≤ d`, contributing
`≤ d e^{2ℓd}/(1 + (T − γ)²)`; the finitely many others contribute `≤ e^{2ℓ}` each. The weighted density
`Σ m/(1 + (T − γ)²) ≤ C log T` (corpus `exists_tsum_weighted_density_le`, transferred from zero copies
by `sum_mult_le_tsum_copies`) bounds the error sums by `c_k(d e^{2ℓd} C log T + e^{2ℓ}N(−T₀, T₀))`.

*Window count.* Littlewood's counting inequality
`Σ mψ₀ ≤ (ℓA)²N(T − δ, T + δ) + δ⁻²Σ mψ₁` needs only summability. With
`Y = (ℓA)²N + Σe₀ + δ⁻²Σe₁` it gives `∫ψ₀ν_X ≤ Y + δ⁻²∫ψ₁ν_X`, and Littlewood's analytic chain
(Plancherel, Stirling, `|ν_X − μ| ≤ 3X²`), with `(ℓA)²N` replaced by `Y`, gives
`Y/ℓ ≥ (E/2) log T − M₀ − 3πE(1 + 3e^{4ℓ})`. Dividing the error sums by `ℓ` gives statement 1 with
`s(ℓ) = (c₀ + c₁ℓ²/D²)/ℓ`.

*Repair.* Under `d e^{2ℓd}s(ℓ)C ≤ E/4` and `8M ≤ E log t`: `ℓA²N ≥ E log t/8 > 0`. A zero with
`|γ − t| ≤ D/ℓ` and `|η| ≤ d` has spectral point within `R = D/ℓ + d` of `t`, so the radius-`R` head
holds `≥ N` copies. Zeros with `|γ − t| < ½` have depth `≤ d`, and `ℓd ≤ 1 ≤ D` gives `d ≤ D/ℓ`, so
`2d² ≤ R²` and `Rℓ ≤ 2D`. The depth–count bound (`localHeatThreshold_le_of_depth_count`) gives
`λ_t ≤ 64R²/N`, and `64R² log t · Eℓ ≤ 512(Rℓ)²A²N ≤ 2048D²A²N`, i.e. `λ_t log t ≤ K/ℓ`.

*Heights with `Ξ(t) = 0`.* Real zeros of `Ξ` are isolated (`eventually_XiC_ne_zero_punctured`). If
`λ_s log s ≤ ε` on a punctured neighbourhood of `t > 1` but `λ_t log t > ε`, pick `y` strictly between
`ε/log t` and `λ_t`; lower semicontinuity of `λ` and continuity of `ε/log s` give a nearby `s` with
`y < λ_s ≤ ε/log s < y`.

*Equivalence.* (⇐) Given `ε`, take `ℓ = max(1, K/ε)` and
`d = min(1/ℓ, E/(4(e²s(ℓ)C + 1)))`; then `ℓd ≤ 1`, `e^{2ℓd} ≤ e²`, and the repair hypothesis holds;
the strip of depth `d` gives `λ_t log t ≤ K/ℓ ≤ ε` at large heights with `Ξ(t) ≠ 0`, hence at all large
heights. (⇒) Given `d`, take `ε = d²/200`. A zero with `|Im ρ| ≥ max(t₀, e^{1600})` and
`|Re ρ − ½| > 0` has a copy among `ρ, ρ̄, 1 − ρ̄, 1 − ρ` with `Re σ − ½ = |Re ρ − ½|` and
`Im σ = |Im ρ|`; detection (`le_localHeatThreshold_of_offLine_zero`) gives
`(Re σ − ½)²/200 ≤ λ_{Im σ} log Im σ ≤ d²/200`.

## What it changes (WP-B, the heat pincer)
The pincer closes exactly when the zeros converge to the line: `λ_t log t → 0` iff the maximal depth
of the zeros above `T` tends to `0`. Neither side is known; the statement is a reformulation, not
progress on either. The rate is weaker than first conjectured: the conjectured linear repair
`λ_t log t ≪ d` is not what the argument gives. Its error budget `d e^{2ℓd}s(ℓ)` grows polynomially
in `ℓ` (`s(ℓ) ≪ ℓ²` from `B₀ ≪ ℓ`), because the pointwise summand bound decays like `(1 + |x|)⁻⁴`
instead of at the window scale `1/ℓ`. So `ℓ ≍ d^{−1/2}` and `λ_t log t ≪ √d` (inference from the
constants, not formalized as a rate). A window-scale bound would need the local count at scale `d`,
which is the A1 input again.

## Log
- 2026-10-31 — created; proved; formalized. The linear-rate statement was replaced by the qualitative
  equivalence and the `K/ℓ` repair.
