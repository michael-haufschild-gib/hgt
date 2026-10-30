import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFlipThresholdGrowsLikeAPowerOfThePrime
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.EveryProfileWithoutRealFourierZerosKeepsAGammaReserve
import GaloisForLFunctions.BiScaleUncertainty.EffectiveTranslatedPairingAndMultiplicityDefect

/-!
# The Gamma reserve survives growing overlap

At growing overlap the atom norms degenerate (adjacent atoms cancel), but the synthesized norm
keeps an explicit floor. The tilted spline's transform is at least `sinh⁴ 1/(8(1 + (101c/8)²)²)` on
`[c, 101c]`, and the Montgomery–Vaughan band bound `∫_N^{101N} |D_x|² ≥ 48N Σ x_n²` transfers
through this profile multiplier. For every `1 ≤ c ≤ N` and every coefficient vector, with
`M = ‖φ‖²` and atom mass `(c/N)M`:

* **synthesized mass** `∫ f_x² ≥ κ c⁻⁷ (c/N)M Σ x_n²` (`integral_atomicTest_sq_ge_growing`);
* **Gamma reserve** `archForm f_x ≥ (κ c⁻⁷ log N − b c)(c/N)M Σ x_n²`
  (`archForm_atomicTest_ge_growing`), the Gamma weight `log |t| ≥ log N` on the band and the
  Gram rows `≤ 1 + 2ec` paying the low frequencies.

The constants are explicit and uniform in `N` and `c`: the reserve per unit atom mass tends to
infinity along every schedule with `c_N⁸ = o(log N)` (`tendsto_gammaReserve_growing`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped Real

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics
  ArithmeticCastelnuovoSeveri BiScaleUncertainty.ChebyshevGauge ArithmeticPositivityTheory

/-- The floor of `|φ̂|²` on the band `[c, 101c]` for the tilted spline. -/
def splineBandFloor (c : ℝ) : ℝ := Real.sinh 1 ^ 8 / (64 * (1 + (101 * c / 8) ^ 2) ^ 4)

theorem splineBandFloor_pos (c : ℝ) : 0 < splineBandFloor c := by
  have := Real.sinh_pos_iff.mpr (zero_lt_one (α := ℝ))
  unfold splineBandFloor; positivity

theorem tiltedUnitSpline_band_floor {c : ℝ} (hc : 0 < c) :
    ∀ t ∈ Set.Icc c (101 * c),
      splineBandFloor c ≤ ‖Zeta23.paperFT (cx tiltedUnitSpline) (t : ℂ)‖ ^ 2 := by
  intro t ht
  have ht0 : 0 ≤ t := hc.le.trans ht.1
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr zero_lt_one
  have hlow := le_norm_paperFT_splineProbe_ofReal (t / 8)
  have hden : (1 + (t / 8) ^ 2) ^ 2 ≤ (1 + (101 * c / 8) ^ 2) ^ 2 := by
    have : (t / 8) ^ 2 ≤ (101 * c / 8) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith [ht.2]) 2
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hnorm : (1 / 8) * (Real.sinh 1 ^ 4 / (1 + (101 * c / 8) ^ 2) ^ 2) ≤
      ‖Zeta23.paperFT (cx tiltedUnitSpline) (t : ℂ)‖ := by
    rw [norm_paperFT_tiltedUnitSpline_eq]
    refine mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_left (by positivity)
      (by positivity) hden).trans hlow) (by norm_num)
  have hsq := pow_le_pow_left₀ (by positivity) hnorm 2
  refine le_trans (le_of_eq ?_) hsq
  unfold splineBandFloor
  field_simp
  ring

/-- The polynomial form of the band floor: `splineBandFloor c ≥ (sinh⁸ 1/(64·161⁴)) c⁻⁸`. -/
theorem splineBandFloor_ge {c : ℝ} (hc : 1 ≤ c) :
    Real.sinh 1 ^ 8 / (64 * 161 ^ 4) / c ^ 8 ≤ splineBandFloor c := by
  have hc0 : 0 < c := by linarith
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr zero_lt_one
  have h1 : 1 + (101 * c / 8) ^ 2 ≤ 161 * c ^ 2 := by nlinarith
  have h4 : (1 + (101 * c / 8) ^ 2) ^ 4 ≤ 161 ^ 4 * c ^ 8 := by
    calc (1 + (101 * c / 8) ^ 2) ^ 4 ≤ (161 * c ^ 2) ^ 4 :=
          pow_le_pow_left₀ (by positivity) h1 4
      _ = 161 ^ 4 * c ^ 8 := by ring
  unfold splineBandFloor
  rw [div_div]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  nlinarith [pow_pos hc0 8]

/-- The constant of the synthesized-mass floor. -/
def growingMassConstant : ℝ :=
  24 * (Real.sinh 1 ^ 8 / (64 * 161 ^ 4)) / (π * ∫ u, tiltedUnitSpline u ^ 2)

theorem growingMassConstant_pos : 0 < growingMassConstant := by
  have := Real.sinh_pos_iff.mpr (zero_lt_one (α := ℝ))
  have := integral_tiltedUnitSpline_sq_pos
  unfold growingMassConstant; positivity

/-- The band mass of the atomic family at overlap `c`. -/
theorem band_mass_ge {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    48 * c ^ 2 * splineBandFloor c / N * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      ∫ t in (N : ℝ)..101 * N,
        ‖Zeta23.paperFT (cx (atomicTest N x (atomDilate tiltedUnitSpline (c / N)))) (t : ℂ)‖ ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h := noRealZero_highBand_mass contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hc0
    (splineBandFloor_pos c) (tiltedUnitSpline_band_floor hc0) hN x
  refine le_trans (le_of_eq ?_) h
  field_simp

/-- **The synthesized-mass floor at growing overlap**:
`∫ f_x² ≥ κ c⁻⁷ (c/N)‖φ‖² Σ x_n²` for every `1 ≤ c` and `N ≥ 1`. -/
theorem integral_atomicTest_sq_ge_growing {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hN : 1 ≤ N)
    (x : ℕ → ℝ) :
    growingMassConstant / c ^ 7 * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      ∫ u, atomicTest N x (atomDilate tiltedUnitSpline (c / N)) u ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc0 hNR
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw
  set f := atomicTest N x (atomDilate tiltedUnitSpline (c / N))
  have hf : ContDiff ℝ 2 f := contDiff_atomicTest hg N x
  have hfc : HasCompactSupport f := hasCompactSupport_atomicTest hgsupp N x
  -- Plancherel: the band is part of the whole spectrum
  have hcf : HasCompactSupport (fun u => (f u : ℂ)) := hfc.comp_left Complex.ofReal_zero
  have hcd : ContDiff ℝ 2 (fun u => (f u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hpl := RHTower.LebesgueAtomWeil.integral_norm_sq_paperFT_eq hcd hcf
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hpl
  have hint : Integrable (fun t : ℝ => ‖Zeta23.paperFT (cx f) (t : ℂ)‖ ^ 2) :=
    integrable_normSq_paperFT_ofReal hf hfc
  have hsub : ∫ t in (N : ℝ)..101 * N, ‖Zeta23.paperFT (cx f) (t : ℂ)‖ ^ 2 ≤
      ∫ t, ‖Zeta23.paperFT (cx f) (t : ℂ)‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_le_integral hint (Eventually.of_forall fun t => sq_nonneg _)
  have hband := band_mass_ge hc hN x
  have hfloor := splineBandFloor_ge hc
  have hM := integral_tiltedUnitSpline_sq_pos
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  have hmain : growingMassConstant / c ^ 7 * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) ≤
      1 / (2 * π) * (48 * c ^ 2 * splineBandFloor c / N) := by
    unfold growingMassConstant
    have hfl : Real.sinh 1 ^ 8 / (64 * 161 ^ 4) ≤ c ^ 8 * splineBandFloor c := by
      rw [div_le_iff₀ (pow_pos hc0 8)] at hfloor; linarith
    rw [show 24 * (Real.sinh 1 ^ 8 / (64 * 161 ^ 4)) / (π * ∫ u, tiltedUnitSpline u ^ 2) / c ^ 7 *
        (c / N * ∫ u, tiltedUnitSpline u ^ 2) =
        24 * (Real.sinh 1 ^ 8 / (64 * 161 ^ 4)) / (π * c ^ 6 * N) by
      field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    have : 1 / (2 * π) * (48 * c ^ 2 * splineBandFloor c / N) * (π * c ^ 6 * N) =
        24 * (c ^ 8 * splineBandFloor c) := by field_simp; ring
    rw [this]
    linarith
  calc _ ≤ 1 / (2 * π) * (48 * c ^ 2 * splineBandFloor c / N) * (∑ n ∈ Icc 1 N, x n ^ 2) :=
        mul_le_mul_of_nonneg_right hmain hS
    _ ≤ 1 / (2 * π) * ∫ t, ‖Zeta23.paperFT (cx f) (t : ℂ)‖ ^ 2 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hband.trans hsub) (by positivity)
    _ = _ := hpl

/-- The low-frequency cost constant of the Gamma reserve. -/
def growingReserveCost : ℝ := (factorialSpanGammaOffset + Real.log 2) * (1 + 2 * Real.exp 1)

/-- **The Gamma reserve at growing overlap**: for every `1 ≤ c ≤ N`,
`archForm f_x ≥ (κ c⁻⁷ log N − b c)(c/N)‖φ‖² Σ x_n²`. -/
theorem archForm_atomicTest_ge_growing {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hcN : c ≤ N)
    (x : ℕ → ℝ) :
    (growingMassConstant / c ^ 7 * Real.log N - growingReserveCost * c) *
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      archForm (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) := by
  have hc0 : 0 < c := by linarith
  have hNR : (0 : ℝ) < N := hc0.trans_le hcN
  have hN : 1 ≤ N := by exact_mod_cast (hc.trans hcN)
  have hw : 0 < c / N := div_pos hc0 hNR
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw
  set f := atomicTest N x (atomDilate tiltedUnitSpline (c / N))
  have hf : ContDiff ℝ 2 f := contDiff_atomicTest hg N x
  have hfc : HasCompactSupport f := hasCompactSupport_atomicTest hgsupp N x
  have hgamma := archForm_ge_log_band_sub_mass hf hfc hNR
  have hband := band_mass_ge hc hN x
  have hmass := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc0 hcN hgsupp x
  rw [integral_atomDilate_sq hw] at hmass
  have hoff : 0 ≤ factorialSpanGammaOffset + Real.log 2 :=
    add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg (by norm_num))
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hM := integral_tiltedUnitSpline_sq_pos
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  have hfloor := splineBandFloor_ge hc
  have hfl : Real.sinh 1 ^ 8 / (64 * 161 ^ 4) ≤ c ^ 8 * splineBandFloor c := by
    rw [div_le_iff₀ (pow_pos hc0 8)] at hfloor; linarith
  -- the band term
  have hbandTerm : growingMassConstant / c ^ 7 * Real.log N *
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      Real.log N / (2 * π) *
        ∫ t in (N : ℝ)..101 * N, ‖Zeta23.paperFT (cx f) (t : ℂ)‖ ^ 2 := by
    have hcoef : growingMassConstant / c ^ 7 * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) ≤
        1 / (2 * π) * (48 * c ^ 2 * splineBandFloor c / N) := by
      unfold growingMassConstant
      rw [show 24 * (Real.sinh 1 ^ 8 / (64 * 161 ^ 4)) / (π * ∫ u, tiltedUnitSpline u ^ 2) /
          c ^ 7 * (c / N * ∫ u, tiltedUnitSpline u ^ 2) =
          24 * (Real.sinh 1 ^ 8 / (64 * 161 ^ 4)) / (π * c ^ 6 * N) by
        field_simp; ring]
      rw [div_le_iff₀ (by positivity)]
      have : 1 / (2 * π) * (48 * c ^ 2 * splineBandFloor c / N) * (π * c ^ 6 * N) =
          24 * (c ^ 8 * splineBandFloor c) := by field_simp; ring
      rw [this]
      linarith
    calc _ = Real.log N * (growingMassConstant / c ^ 7 *
          ((c / N) * ∫ u, tiltedUnitSpline u ^ 2)) * (∑ n ∈ Icc 1 N, x n ^ 2) := by ring
      _ ≤ Real.log N * (1 / (2 * π) * (48 * c ^ 2 * splineBandFloor c / N)) *
          (∑ n ∈ Icc 1 N, x n ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hlogN) hS
      _ = Real.log N / (2 * π) *
          (48 * c ^ 2 * splineBandFloor c / N * (∑ n ∈ Icc 1 N, x n ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hband (by positivity)
  -- the low-frequency cost
  have hcostTerm : (factorialSpanGammaOffset + Real.log 2) * (∫ u, f u ^ 2) ≤
      growingReserveCost * c * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        (∑ n ∈ Icc 1 N, x n ^ 2) := by
    have hB : 1 + 2 * Real.exp 1 * c ≤ (1 + 2 * Real.exp 1) * c := by
      have := Real.exp_pos 1; nlinarith
    calc _ ≤ (factorialSpanGammaOffset + Real.log 2) *
          ((c / N * ∫ u, tiltedUnitSpline u ^ 2) * (1 + 2 * Real.exp 1 * c) *
            ∑ n ∈ Icc 1 N, x n ^ 2) := mul_le_mul_of_nonneg_left hmass hoff
      _ ≤ (factorialSpanGammaOffset + Real.log 2) *
          ((c / N * ∫ u, tiltedUnitSpline u ^ 2) * ((1 + 2 * Real.exp 1) * c) *
            ∑ n ∈ Icc 1 N, x n ^ 2) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hB (by positivity)) hS) hoff
      _ = _ := by unfold growingReserveCost; ring
  linarith

/-- **The reserve grows along every schedule `c_N⁸ = o(log N)`.** -/
theorem tendsto_gammaReserve_growing {c : ℕ → ℝ} (hc : ∀ᶠ N in atTop, 1 ≤ c N)
    (hgrowth : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => growingMassConstant / c N ^ 7 * Real.log N - growingReserveCost * c N)
      atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hK := growingMassConstant_pos
  have hcost : 0 ≤ growingReserveCost := by
    unfold growingReserveCost
    exact mul_nonneg (add_nonneg factorialSpanGammaOffset_nonneg
      (Real.log_nonneg (by norm_num))) (by positivity)
  -- `log N / c_N⁷ ≥ c_N · (log N/c_N⁸) → ∞` and `c_N ≤ (log N / c_N⁷)·(c_N⁸/log N)`
  have hratio : Tendsto (fun N : ℕ => Real.log N / c N ^ 8) atTop atTop := by
    have hpos : ∀ᶠ N : ℕ in atTop, 0 < c N ^ 8 / Real.log N := by
      filter_upwards [hc, hlog.eventually_gt_atTop 0] with N h1 h2
      positivity
    have := (tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hgrowth, hpos⟩))
    refine this.congr' ?_
    filter_upwards [hc, hlog.eventually_gt_atTop 0] with N h1 h2
    simp [Function.comp, inv_div]
  refine tendsto_atTop.mpr fun B => ?_
  filter_upwards [hc, hratio.eventually_ge_atTop ((B + 1) / (growingMassConstant / 2) + 1),
    hgrowth.eventually (gt_mem_nhds (show (0 : ℝ) < growingMassConstant / (2 * growingReserveCost + 1) by
      positivity)), hlog.eventually_gt_atTop 0]
    with N h1 hbig hsmall hL
  set C := c N
  set L := Real.log N
  have hC0 : 0 < C := by linarith
  have hC7 : 0 < C ^ 7 := pow_pos hC0 7
  have hC8 : 0 < C ^ 8 := pow_pos hC0 8
  -- the cost is at most half the gain: `cost·C ≤ (K/2) L/C⁷` since `C⁸/L` is small
  have hhalf : growingReserveCost * C ≤ growingMassConstant / 2 * (L / C ^ 7) := by
    have h := hsmall
    rw [div_lt_div_iff₀ hL (by positivity)] at h
    rw [show growingMassConstant / 2 * (L / C ^ 7) = growingMassConstant * L / (2 * C ^ 7) by ring,
      le_div_iff₀ (by positivity)]
    have : C ^ 8 = C * C ^ 7 := by ring
    nlinarith
  -- the gain: `(K/2) L/C⁷ ≥ (K/2) L/C⁸ ≥ B + 1` since `C ≥ 1`
  have hgain : (B + 1) ≤ growingMassConstant / 2 * (L / C ^ 7) := by
    have hL8 : L / C ^ 8 ≤ L / C ^ 7 := by
      refine div_le_div_of_nonneg_left hL.le hC7 ?_
      have : C ^ 7 * 1 ≤ C ^ 7 * C := mul_le_mul_of_nonneg_left h1 hC7.le
      nlinarith
    have hb : (B + 1) / (growingMassConstant / 2) ≤ L / C ^ 8 := by linarith
    rw [div_le_iff₀ (by positivity)] at hb
    nlinarith
  have : growingMassConstant / C ^ 7 * L = growingMassConstant / 2 * (L / C ^ 7) * 2 := by ring
  linarith

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
