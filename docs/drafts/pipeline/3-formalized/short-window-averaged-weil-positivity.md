# Averaged Weil positivity on windows of length Γ^{99/100} (Q1 / B3.7)

- **ID:** short-window-averaged-weil-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-2510/hard-obstacles-summary.md` Q1, B3.7, milestone (1).
- **Statement.** There are `κ₀ > 0`, `C₀ ≥ 0` and `Γ₀` such that for `Γ ≥ Γ₀`,
  `Γ^{99/100} ≤ H ≤ Γ/8`, `0 ≤ A ≤ κ₀ log Γ` and real `F₀ ∈ C²_c([−A, A])`:
  `(1/H) ∫_Γ^{Γ+H} [Q(F₀ cos γ·) + Q(F₀ sin γ·)] dγ ≥ (1/16) log Γ ‖F₀‖² − C₀ Γ^{−1/2} N(F₀)²`,
  `Q` the complete Weil form, `N` the envelope norm. So Q1 has answer *yes* with `θ = 99/100`.

## Lean
- `RHTower.exists_shortWindowZeros_weighted_le`, `RHTower.exists_shortWindowZeros_count_le`,
  `RHTower.exists_selberg_shortWindow_nearLine_zeroDensity`
  (`formal/GaloisForLFunctions/RHTower/SelbergShortWindowNearLineDensity.lean`).
- `GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_shortWindow_frequencyAverage_quadrature_pos`,
  with `integral_window_tsum_depthDiff_le`, `integral_window_norm_paperFT_depthSum_sq_ge`,
  `exists_window_core_count`, `exists_window_shell_le`
  (`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ShortWindowAveragedWeilPositivity.lean`).
- Axioms: `propext`, `Classical.choice`, `Quot.sound`. Wired into `RHTower.lean` and
  `ArithmeticCastelnuovoSeveri.lean`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof
Write `Q(F₀ cos γ·) + Q(F₀ sin γ·) = Re W(F₀e^{iγ·}, F₀e^{iγ·})`. For a finite set `C` of zeros,
`Re W ≥ Σ_{ρ∈C} m_ρ ‖F̂(depthSum_ρ)(−γ)‖² − Σ_ρ m_ρ d_ρ(γ)`, `d_ρ(γ) = ‖F̂(γ_ρ−γ) − F̂(γ̄_ρ−γ)‖²/4`
(`re_zeta_W_complexModulatedSource_ge_finset`). Integrate over `[Γ, Γ+H]` and divide by `H`.

1. **Lorentz decay.** For `0 < Re ρ < 1`, `‖F̂(γ_ρ − ω)‖, ‖F̂(γ̄_ρ − ω)‖ ≤ e^{A/2}N/(1 + (Im ρ − ω)²)`,
   so `d_ρ(ω)` and `‖F̂(depthSum_ρ)(−ω)‖²` are `≤ e^A N² (1 + (Im ρ − ω)²)^{−2}`.
2. **Remote zeros.** If `|Im ρ − γ| ≥ H` then `(1 + x²)^{−2} ≤ H^{−2}(1 + x²)^{−1}`; the Lorentzian mass
   at height `γ` is `≤ 8(c + log(|γ| + 4))`. Hence
   `∫_window Σ_ρ m_ρ d_ρ ≤ Σ_{G_loc} ∫ d_q + 8(c + log(2Γ+4)) e^A N²/H`, `G_loc` the copies with
   ordinate in `[Γ − H, Γ + 2H]`.
3. **Local weights.** `∫_window d_q ≤ 4 w_A(q) ‖F₀‖²`, `w_A(q) = min((π/2)e^{2Aδ_q}, 2πA²δ_q² e^{2Aδ_q})`,
   `δ_q = |Re q − 1/2|`.
4. **Core.** For `Im ρ ∈ [Γ + H/4, Γ + 3H/4]`, Plancherel gives `∫_ℝ ‖F̂(depthSum_ρ)(−γ)‖² ≥ 2π‖F₀‖²`
   and, by step 1, the complement of the window carries `≤ 16π e^A N²/H²`. Riemann–von Mangoldt on
   short windows (`exists_xiPosZeroCount_window_bounds`, error `O(log Γ)`, and `H ≥ Γ^{1/2} ≥ 64πC`)
   gives core multiplicity between `H log Γ/(16π)` and `H log Γ`. Core total:
   `≥ (1/8)H log Γ ‖F₀‖² − 16π log Γ e^A N²/H`.
5. **Shell.** Fix `ε = 1/16`. Shallow copies (`δ_q ≤ C₂/log Γ`): `w_A ≤ 6πC₂²κ₀²`, and the window
   `[Γ − H, Γ + 2H]` holds `≤ 3H log Γ` copies (`exists_xiZeroCount_window_le`); with
   `κ₀² ≤ ε/(36πC₂²)` they cost `≤ (ε/2) H log Γ`. Deep copies: `w_A ≤ (π/2)e^{(δ_q/19200) log U}` for
   `U = 3Γ` when `κ₀ ≤ 1/38400`. Selberg's mollified mean-square bound holds on every
   `[B, B+W] ⊂ [U/4, U/2]` with `W ≥ U^{99/100} + 2`, admissible heights chosen in `(B, B+1)` and
   `(B+W−1, B+W)`: `#{Re ρ ≥ 1/2 + v, Im ρ ∈ [T₁, T₂]} ≤ ((T₂−T₁)A e^{−vL/2400} + KL)/(πv)`. Dyadic
   shells in `v` give the weighted count
   `Σ e^{λδL} ≤ (T₂−T₁)A/(πv₀)(1 + 4800/(v₀L))e^{−v₀L/4800} + L·KL/(πv₀)e^{λL}`. Take
   `B = Γ − H − 2`, `W = 3H + 4`, `v₀ = C₂/log Γ`, `C₂ ≥ max(4800, 64A/ε)`: the first term is
   `≤ (8A/(πC₂)) H log Γ`, the second `O(Γ^{3/4})`, and after division by `H ≥ Γ^{99/100}` the deep
   copies cost `≤ (ε/2) log Γ`.
6. **Assembly.** `(1/H)∫ ≥ (1/8) log Γ ‖F₀‖² − (1/16) log Γ ‖F₀‖² − errors`, and every error is
   `e^A (log Γ) H^{−2} N² ≤ Γ^{1/2}·KΓ^{1/6}·Γ^{−198/100} N² ≤ KΓ^{−1/2}N²` since `e^A ≤ Γ^{1/2}`.

## What θ = 99/100 measures
The only place `θ` enters is the admissible-window length `U^{99/100}` of the Selberg mollifier
(`exists_admissible_heights_of_mollifier`). Every other step works for `H ≥ Γ^{1/2+}`. A smaller
`θ` therefore needs a near-line density bound on windows shorter than `U^{99/100}`, i.e. the
short-interval mean square of the mollified `ζ` at that length.
