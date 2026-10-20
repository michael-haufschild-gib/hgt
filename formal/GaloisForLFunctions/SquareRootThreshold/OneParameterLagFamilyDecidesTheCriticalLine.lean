import GaloisForLFunctions.SquareRootThreshold.DifferenceTwoBumpTestsDecideTheCriticalLine

/-!
# One parameter decides the critical line

Fix a width `w` and take the unmodulated bump `κ_w`. The difference tests

`f_v(t) = κ_w(t + v/2) − κ_w(t − v/2)`,  `v ≥ 0`,

form a one-parameter family. For all but countably many widths it decides the line.

* **No cancellation at the center `0`** (`evenCoeff_modScaledBump_zero`). For the zero
  `t = ½ + δ + iγ`, the merged coefficient of `e^{(δ + iγ)v}` in `2 Re S(v)` is
  `(m_t + m_{t̄}) h_w(γ − iδ)²`, `h_w` the transform of `κ_w`. Since `h_w` is even, the
  conjugate zero `t̄` adds to `t` instead of cancelling it. The coefficient vanishes only where
  `h_w` does.
* **Generic widths** (`countable_bad_widths`). `h_w(p) = 4w ĥ(4wp)` with `ĥ` the transform of the
  fixed bump, an entire function with `ĥ(0) = ∫κ > 0`. So only countably many widths have
  `h_w(p) = 0` (`countable_setOf_paperFT_scaledBump_eq_zero`). The zeros of a configuration
  are countable, so all but countably many widths see every off-line zero.

**One parameter decides the line** (`onLine_iff_lag_twoBump_nonneg`). Let `Z` be tempered without
real zeros, and let `w > 0` be such that `h_w` vanishes at no `γ_ρ`, `ρ` off-line. Then all zeros lie
on the critical line iff `Re W(f_v, f_v) ≥ 0` for every lag `v ≥ V`, for any fixed `V`. The proof is
the one-sided Landau argument of `evenCoeff_eq_zero_of_difference_nonneg`, at the single center
`0`.

For `ζ` (`zeta_onLine_iff_lag_primeWindow_nonneg`): for all but countably many `w ∈ (0, ½ log 2)`,
RH holds iff the window functional `P_v` of `f_v ⋆ f̃_v` is nonnegative for every `v ≥ V`. That is
one real inequality per dyadic window `(X/2, 2X)`, `X = e^v`, over all `X ≥ e^V`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **No cancellation at the center `0`.** For the zero `½ + z`, the merged coefficient of the
unmodulated bump is `(m_{½+z} + m_{½+z̄}) h_w(−iz)²`. -/
theorem evenCoeff_modScaledBump_zero (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) {z : ℂ}
    (hz : (1 / 2 + z) ∈ Z.carrier) :
    evenCoeff Z (modScaledBump w 0) z =
      ((Z.mult (1 / 2 + z) : ℂ) + Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) (1 / 2 + conj z)) *
        paperFT (scaledBump w) (-(I * z)) ^ 2 := by
  rw [evenCoeff, lagCoeff_modScaledBump Z hw 0 hz, Complex.ofReal_zero, sub_zero, add_mul]
  congr 1
  by_cases hzc : (1 / 2 + conj z) ∈ Z.carrier
  · rw [lagCoeff_modScaledBump Z hw 0 hzc, Complex.ofReal_zero, sub_zero, map_mul,
      Complex.conj_natCast, map_pow, conj_paperFT_scaledBump, Set.indicator_of_mem hzc]
    congr 2
    rw [← paperFT_scaledBump_neg w]
    congr 1
    simp [map_neg, map_mul]
  · rw [lagCoeff, Set.indicator_of_notMem hzc, Set.indicator_of_notMem hzc, map_zero, zero_mul]

/-- **Generic widths.** For `p ≠ 0`, the transform `h_w(p)` vanishes for only countably many
widths `w > 0`. -/
theorem countable_setOf_paperFT_scaledBump_eq_zero {p : ℂ} :
    {w : ℝ | 0 < w ∧ paperFT (scaledBump w) p = 0}.Countable := by
  set g : ℂ → ℂ := fun ζ => paperFT weilBumpC (4 * ζ * p) with hg
  have hcont : Continuous weilBumpC := contDiff_weilBumpC.continuous
  have hdiff : Differentiable ℂ g :=
    (WeilEF.differentiable_paperFT hcont hasCompactSupport_weilBumpC).comp
      (((differentiable_const _).mul differentiable_id).mul (differentiable_const _))
  have hg0 : g 0 ≠ 0 := by
    have hpos : (0 : ℝ) < ∫ u, weilBump u := weilBump.integral_pos
    have e : g 0 = ((∫ u, weilBump u : ℝ) : ℂ) := by
      simp only [hg, mul_zero, zero_mul, paperFT, Complex.exp_zero, mul_one]
      exact integral_complex_ofReal
    rw [e]
    exact_mod_cast hpos.ne'
  have hcod := (hdiff.differentiableOn.analyticOnNhd isOpen_univ).preimage_zero_mem_codiscreteWithin
    hg0 (Set.mem_univ 0) isConnected_univ
  have hZ : (g ⁻¹' {0} ∩ Set.univ).Countable :=
    (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
      (isDiscrete_of_codiscreteWithin (by simpa using hcod))
  rw [Set.inter_univ] at hZ
  refine (hZ.preimage Complex.ofReal_injective).mono fun w ⟨hw, h0⟩ => ?_
  show g (w : ℂ) = 0
  rw [paperFT_scaledBump hw, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (by exact_mod_cast (by positivity : (4 * w : ℝ) ≠ 0))
  · rw [hg]
    simpa [mul_assoc] using h0

/-- **The bad widths of a configuration are countable.** -/
theorem countable_bad_widths (Z : ZeroConfig) :
    {w : ℝ | 0 < w ∧ ∃ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 ∧
      paperFT (scaledBump w) (gammaOf ρ) = 0}.Countable := by
  have hsub : {w : ℝ | 0 < w ∧ ∃ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 ∧
      paperFT (scaledBump w) (gammaOf ρ) = 0} ⊆
      ⋃ ρ ∈ Z.carrier, {w : ℝ | 0 < w ∧ paperFT (scaledBump w) (gammaOf ρ) = 0} :=
    fun w ⟨hw, ρ, hρ, _, h0⟩ => Set.mem_biUnion hρ ⟨hw, h0⟩
  exact ((carrier_countable Z).biUnion fun ρ _ =>
    countable_setOf_paperFT_scaledBump_eq_zero).mono hsub

/-- **One parameter decides the line.** Let `Z` be tempered without real zeros, `w > 0` a width
whose transform `h_w` vanishes at no `γ_ρ` of an off-line zero, and `V ∈ ℝ`. All zeros lie on the
critical line iff `Re W ≥ 0` on every test `κ_w(t + v/2) − κ_w(t − v/2)`, `v ≥ V`. -/
theorem onLine_iff_lag_twoBump_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) (V : ℝ) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔ ∀ v : ℝ, V ≤ v →
      0 ≤ (Z.W (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re := by
  refine ⟨fun hon _ _ => weil_nonneg_of_onLine Z hon _, fun h ρ hρ => ?_⟩
  by_contra hre
  obtain ⟨t, ht, -⟩ := exists_rightZero_of_offLine Z hρ hre
  -- the right zero `t` is seen by `h_w`
  have hgt : paperFT (scaledBump w) (gammaOf t) ≠ 0 := hgood t ht.1 (by linarith [ht.2])
  have hz : (1 / 2 + (t - 1 / 2)) ∈ Z.carrier := by rw [add_sub_cancel]; exact ht.1
  have hzre : 0 < (t - 1 / 2).re := by simp; linarith [ht.2]
  have h0 := evenCoeff_eq_zero_of_difference_nonneg Z hZ (contDiff_modScaledBump_two w 0)
    (modScaledBump_support hw 0) hreal (V := V) h hzre
  rw [evenCoeff_modScaledBump_zero Z hw hz] at h0
  have hγt : -(I * (t - 1 / 2)) = gammaOf t := by
    rw [gammaOf, Complex.div_I]; ring
  rw [hγt] at h0
  have hm : (1 : ℝ) ≤ Z.mult (1 / 2 + (t - 1 / 2)) := by exact_mod_cast Z.one_le_mult _ hz
  have hsum : ((Z.mult (1 / 2 + (t - 1 / 2)) : ℂ) +
      Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) (1 / 2 + conj (t - 1 / 2))) ≠ 0 := by
    intro h1
    have h2 := congrArg Complex.re h1
    by_cases hc : (1 / 2 + conj (t - 1 / 2)) ∈ Z.carrier
    · rw [Set.indicator_of_mem hc, Complex.add_re, Complex.natCast_re, Complex.natCast_re,
        Complex.zero_re] at h2
      linarith [(Nat.cast_nonneg (Z.mult (1 / 2 + conj (t - 1 / 2))) : (0 : ℝ) ≤ _)]
    · rw [Set.indicator_of_notMem hc, Complex.add_re, Complex.natCast_re, Complex.zero_re] at h2
      linarith
  exact (mul_ne_zero hsum (pow_ne_zero 2 hgt)) h0

/-- **For `ζ`: one inequality per dyadic window.** For all but countably many widths
`w ∈ (0, ½ log 2)` and every `V ≥ 0`, RH holds iff the window functional `P_v` of the
autocorrelation of `κ_w(t + v/2) − κ_w(t − v/2)` is nonnegative for every lag `v ≥ V`. -/
theorem zeta_onLine_iff_lag_primeWindow_nonneg :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E →
      ∀ V : ℝ, 0 ≤ V → ((∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔ ∀ v : ℝ, V ≤ v →
        0 ≤ (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
          (twoBump (modScaledBump w 0) v (-1)))).re) := by
  refine ⟨_, countable_bad_widths zetaZeroConfig, fun w hw hw2 hwE V hV => ?_⟩
  have hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  refine (onLine_iff_lag_twoBump_nonneg _ temperedConfig_zetaZeroConfig zetaZeroConfig_im_ne_zero
    hw hgood V).trans (forall_congr' fun v => imp_congr_right fun hv => ?_)
  rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 (hV.trans hv)]

end GaloisForLFunctions.SquareRootThreshold
