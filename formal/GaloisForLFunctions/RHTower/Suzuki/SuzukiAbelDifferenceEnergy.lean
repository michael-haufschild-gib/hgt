import GaloisForLFunctions.RHTower.Suzuki.SuzukiAbelDifferencePlancherel

/-!
# Finiteness of the Abel difference energy of a Schwartz function

For `δ > 0` and Schwartz `f`, the spectral density `log(1 + (2πξ/δ)^2) |𝓕f(ξ)|^2` is integrable,
since `log(1 + u) ≤ u` dominates it by `(2π/δ)^2 |ξ|^2 |𝓕f(ξ)| sup|𝓕f|`. Hence the spectral Abel
energy is the real integral of this density, and by the Abel difference Plancherel identity the
physical energy `∫_0^∞ (e^(-δh) / h) ∫ |f(x) - f(x + h)|^2 dx dh` is finite.

## Main results

- `integrable_abelSchwartzSpectralDensity`: `ξ ↦ log(1 + (2πξ/δ)^2) |𝓕f(ξ)|^2` is integrable.
- `abelSchwartzSpectralEnergyL_eq_ofReal_integral`: the spectral energy is the real integral of
  that density.
- `abelSchwartzPhysicalEnergyL_lt_top`: the physical Abel difference energy is finite.

## Hypotheses

Unconditional for Schwartz `f`, assuming only `δ > 0`.
-/

open Complex Filter MeasureTheory Set
open FourierTransform
open scoped Topology

namespace RHTower

noncomputable section

/-- For `δ > 0` and Schwartz `f`, the spectral density `log(1 + (2πξ/δ)^2) |𝓕f(ξ)|^2` is integrable
on `ℝ`. -/
theorem integrable_abelSchwartzSpectralDensity
    {delta : ℝ} (hdelta : 0 < delta) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun xi : ℝ =>
      Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) *
        ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) := by
  let F : SchwartzMap ℝ ℂ := 𝓕 f
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0 F
  let K : ℝ := (2 * Real.pi / delta) ^ 2
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hK0 : 0 ≤ K := sq_nonneg _
  have hbase : Integrable (fun xi : ℝ => |xi| ^ 2 * ‖F xi‖) := by
    simpa [Real.norm_eq_abs] using F.integrable_pow_mul (volume : Measure ℝ) 2
  have hmajor : Integrable (fun xi : ℝ => (K * C) * (|xi| ^ 2 * ‖F xi‖)) :=
    hbase.const_mul (K * C)
  refine hmajor.mono' ?_ ?_
  · have hfcont := GaloisForLFunctions.RHTower.continuous_fourier_of_integrable f.integrable
    exact ((Real.measurable_log.comp
      (measurable_const.add (((measurable_const.mul measurable_id).div_const delta).pow_const 2))).mul
        (hfcont.norm.measurable.pow_const 2)).aestronglyMeasurable
  · filter_upwards with xi
    have hargpos : 0 < 1 + ((2 * Real.pi * xi) / delta) ^ 2 := by positivity
    have hlog : Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) ≤
        ((2 * Real.pi * xi) / delta) ^ 2 := by
      have := Real.log_le_sub_one_of_pos hargpos
      linarith
    have hlog0 : 0 ≤ Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) :=
      Real.log_nonneg (by nlinarith [sq_nonneg ((2 * Real.pi * xi) / delta)])
    have hF : ‖F xi‖ ≤ C := SchwartzMap.norm_le_seminorm ℂ F xi
    have hfreq : ((2 * Real.pi * xi) / delta) ^ 2 = K * |xi| ^ 2 := by
      dsimp [K]
      rw [sq_abs]
      field_simp [hdelta.ne']
    have hclassical : 𝓕 (f : ℝ → ℂ) xi = F xi := by
      dsimp [F]
      exact (congrFun (SchwartzMap.fourier_coe f) xi).symm
    rw [hclassical]
    have hcalc :
      Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) * ‖F xi‖ ^ 2 ≤
          ((2 * Real.pi * xi) / delta) ^ 2 * ‖F xi‖ ^ 2 := by gcongr
    calc
      ‖Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) * ‖F xi‖ ^ 2‖ =
          Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) * ‖F xi‖ ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hlog0 (sq_nonneg _))]
      _ ≤ ((2 * Real.pi * xi) / delta) ^ 2 * ‖F xi‖ ^ 2 := hcalc
      _ = (K * |xi| ^ 2 * ‖F xi‖) * ‖F xi‖ := by rw [hfreq]; ring
      _ ≤ (K * |xi| ^ 2 * ‖F xi‖) * C := by gcongr
      _ = K * C * (|xi| ^ 2 * ‖F xi‖) := by ring

/-- For `δ > 0`, the spectral Abel energy equals the (finite) real integral
`∫ log(1 + (2πξ/δ)^2) |𝓕f(ξ)|^2 dξ`. -/
theorem abelSchwartzSpectralEnergyL_eq_ofReal_integral
    {delta : ℝ} (hdelta : 0 < delta) (f : SchwartzMap ℝ ℂ) :
    abelSchwartzSpectralEnergyL delta f = ENNReal.ofReal
      (∫ xi : ℝ, Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) *
        ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) := by
  unfold abelSchwartzSpectralEnergyL
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_abelSchwartzSpectralDensity hdelta f)
    (Filter.Eventually.of_forall fun xi =>
      mul_nonneg (Real.log_nonneg
        (by nlinarith [sq_nonneg ((2 * Real.pi * xi) / delta)])) (sq_nonneg _))).symm

/-- For `δ > 0` and Schwartz `f`, the physical Abel difference energy
`∫_0^∞ (e^(-δh) / h) ∫ |f(x) - f(x + h)|^2 dx dh` is finite. -/
theorem abelSchwartzPhysicalEnergyL_lt_top
    {delta : ℝ} (hdelta : 0 < delta) (f : SchwartzMap ℝ ℂ) :
    abelSchwartzPhysicalEnergyL delta f < ⊤ := by
  rw [abelSchwartzPhysicalEnergyL_eq_spectralEnergy hdelta,
    abelSchwartzSpectralEnergyL_eq_ofReal_integral hdelta]
  exact ENNReal.ofReal_lt_top

end
end RHTower
