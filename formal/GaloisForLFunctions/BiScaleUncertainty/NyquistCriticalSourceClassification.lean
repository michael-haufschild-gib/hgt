import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalBroadTests
import GaloisForLFunctions.RHTower.LogWindowPrimeNumberTheorem
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftAveragedKernel

/-!
# Fixed-source classification of critical Nyquist escape

The signed expansion applies to the actual normalized correlations of stretched
compact sources. Source regularity supplies every constant. Ordinary source mean
determines the linear coefficient, while normalized archimedean energy vanishes.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators CompactlySupported NNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty
set_option autoImplicit false

private theorem compactSource_mass_pos (f : C_c(ℝ, ℝ)) (hf : f ≠ 0) :
    0 < autocorr f 0 := by
  have hex : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf
    ext x
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hex
  unfold autocorr
  simp only [add_zero]
  exact (f.continuous.mul f.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
    f.hasCompactSupport.mul_right (fun u => mul_self_nonneg (f u)) (x := x)
    (mul_ne_zero hx hx)

/-- The actual normalized correlation, packaged with its proven compact support. -/
def nyquistNormalizedCorrelation (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨fun x => autocorr f x / autocorr f 0, (continuous_autocorr_compact f).div_const _⟩,
    by
      have hs : HasCompactSupport (fun x => autocorr f x * (autocorr f 0)⁻¹) :=
        (hasCompactSupport_autocorr f.hasCompactSupport).mul_right
      simpa only [div_eq_mul_inv] using hs⟩

theorem nyquistNormalizedCorrelation_zero (f : C_c(ℝ, ℝ)) (hf : f ≠ 0) :
    nyquistNormalizedCorrelation f 0 = 1 := div_self (compactSource_mass_pos f hf).ne'

/-- The half-line correlation mass is the squared ordinary source mean divided by twice its mass. -/
theorem integral_Ioi_nyquistNormalizedCorrelation (f : C_c(ℝ, ℝ)) :
    (∫ x in Ioi (0 : ℝ), nyquistNormalizedCorrelation f x) =
      (∫ u, f u) ^ 2 / (2 * autocorr f 0) := by
  have hi : Integrable (nyquistNormalizedCorrelation f : ℝ → ℝ) :=
    (nyquistNormalizedCorrelation f).continuous.integrable_of_hasCompactSupport
      (nyquistNormalizedCorrelation f).hasCompactSupport
  have he : ∀ x, nyquistNormalizedCorrelation f (-x) = nyquistNormalizedCorrelation f x := by
    intro x
    change autocorr f (-x) / autocorr f 0 = autocorr f x / autocorr f 0
    rw [autocorr_neg]
  rw [ArithmeticCriticalityTheory.integral_Ioi_eq_half_of_even hi he]
  change (1 / 2 : ℝ) * (∫ x, autocorr f x / autocorr f 0) = _
  simp only [div_eq_mul_inv, mul_inv_rev, integral_mul_const, integral_autocorr_eq_sq_integral]
  ring

/-- The exact correlation Lipschitz constant supplied by a source Lipschitz constant. -/
def nyquistCorrelationLipschitzConstant (f : C_c(ℝ, ℝ)) (K : ℝ≥0) : ℝ≥0 :=
  (K * ⟨∫ u, |f u|, integral_nonneg (fun u => abs_nonneg (f u))⟩) /
    ⟨autocorr f 0, by
      unfold autocorr
      simp only [add_zero]
      exact integral_nonneg (fun u => mul_self_nonneg (f u))⟩

/-- Every source Lipschitz constant gives the stated normalized correlation constant. -/
theorem lipschitzWith_nyquistNormalizedCorrelation_of_source (f : C_c(ℝ, ℝ))
    (hne : f ≠ 0) {K : ℝ≥0} (hK : LipschitzWith K (f : ℝ → ℝ)) :
    LipschitzWith (nyquistCorrelationLipschitzConstant f K) (nyquistNormalizedCorrelation f) := by
  have hQ := compactSource_mass_pos f hne
  have hbridge (x : ℝ) : RHTower.WeilOneSided.autoCorr f (-x) = autocorr f x := by
    simp only [RHTower.WeilOneSided.autoCorr, autocorr, sub_neg_eq_add]
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  have hb := RHTower.WeilOneSided.abs_autoCorr_sub_le f.continuous f.hasCompactSupport hK (-x) (-y)
  change |RHTower.WeilOneSided.autoCorr f (-x) - RHTower.WeilOneSided.autoCorr f (-y)| ≤
    ((K : ℝ) * ∫ t, |f t|) * |-x - -y| at hb
  rw [hbridge, hbridge, neg_sub_neg, abs_sub_comm y x] at hb
  rw [Real.dist_eq, Real.dist_eq]
  change |autocorr f x / autocorr f 0 - autocorr f y / autocorr f 0| ≤
    ((K : ℝ) * (∫ u, |f u|) / autocorr f 0) * |x - y|
  rw [← sub_div, abs_div, abs_of_pos hQ]
  calc
    _ ≤ ((K : ℝ) * (∫ u, |f u|) * |x - y|) / autocorr f 0 :=
      div_le_div_of_nonneg_right hb hQ.le
    _ = _ := by ring

/-- A fixed smooth source supplies a global Lipschitz constant; no energy-only regularity premise. -/
theorem exists_lipschitzWith_nyquistNormalizedCorrelation (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) :
    ∃ A : ℝ≥0, LipschitzWith A (nyquistNormalizedCorrelation f) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport f.hasCompactSupport hf (by norm_num)
  exact ⟨nyquistCorrelationLipschitzConstant f K,
    lipschitzWith_nyquistNormalizedCorrelation_of_source f hne hK⟩

/-- Pointwise normalized correlation of the actual stretched source. -/
theorem normalized_sourceRescale_eq_nyquistNormalizedCorrelation (f : C_c(ℝ, ℝ))
    (hf : f ≠ 0) {L : ℝ} (hL : 0 < L) (x : ℝ) :
    autocorr (sourceRescale f L⁻¹) x / autocorr (sourceRescale f L⁻¹) 0 =
      nyquistNormalizedCorrelation f (x / L) := by
  change (_ / _) = autocorr f (x / L) / autocorr f 0
  rw [autocorr_sourceRescale f (inv_pos.mpr hL),
    autocorr_sourceRescale f (inv_pos.mpr hL), mul_zero, inv_inv]
  have hQ := (compactSource_mass_pos f hf).ne'
  rw [div_eq_mul_inv x L, mul_comm L⁻¹ x]
  field_simp [hL.ne', hQ]

/-- Residual of the actual stretched source, normalized by its actual squared norm. -/
def nyquistCriticalSourceResidual (m : ℕ) (f : C_c(ℝ, ℝ)) (L : ℝ) : ℝ :=
  ∫ x, (autocorr (sourceRescale f L⁻¹) x / autocorr (sourceRescale f L⁻¹) 0) *
    nyquistWeightKernel ((m : ℝ) + 1) m 0 x

/-- Exact leading coefficient in terms of the source's ordinary mean and squared norm. -/
def nyquistCriticalSourceSlope (m : ℕ) (f : C_c(ℝ, ℝ)) : ℝ :=
  nyquistCriticalConstant m * (∫ u, f u) ^ 2 / (2 * ∫ u, (f u) ^ 2)

private theorem autocorr_zero_eq_integral_sq (f : C_c(ℝ, ℝ)) :
    autocorr f 0 = ∫ u, (f u) ^ 2 := by
  simp only [autocorr, add_zero, sq]

theorem nyquistCriticalSourceResidual_eq_broadTest (m : ℕ) (f : C_c(ℝ, ℝ))
    (hf : f ≠ 0) {L : ℝ} (hL : 0 < L) :
    nyquistCriticalSourceResidual m f L =
      ∫ x, nyquistNormalizedCorrelation f (x / L) * nyquistWeightKernel ((m : ℝ) + 1) m 0 x := by
  unfold nyquistCriticalSourceResidual
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change autocorr (sourceRescale f L⁻¹) x / autocorr (sourceRescale f L⁻¹) 0 * _ = _
    rw [normalized_sourceRescale_eq_nyquistNormalizedCorrelation f hf hL]

/-- The fixed-source expansion for any certified correlation Lipschitz constant. -/
theorem abs_nyquistCriticalSource_error_le (m : ℕ) (f : C_c(ℝ, ℝ))
    (hne : f ≠ 0) {A : ℝ≥0} (hA : LipschitzWith A (nyquistNormalizedCorrelation f))
    {L : ℝ} (hL : 0 < L) :
    |nyquistCriticalSourceResidual m f L - nyquistCriticalSourceSlope m f * L -
        nyquistCriticalFinitePart m| ≤
      (8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) * (A : ℝ) / L := by
  have hb := abs_nyquistCriticalBroadTest_full_error_le m (nyquistNormalizedCorrelation f) hA hL
  rw [← nyquistCriticalSourceResidual_eq_broadTest m f hne hL,
    integral_Ioi_nyquistNormalizedCorrelation, nyquistNormalizedCorrelation_zero f hne, mul_one] at hb
  have hs : nyquistCriticalConstant m * L * ((∫ u, f u) ^ 2 / (2 * autocorr f 0)) =
      nyquistCriticalSourceSlope m f * L := by
    rw [nyquistCriticalSourceSlope, ← autocorr_zero_eq_integral_sq]
    ring
  rwa [hs] at hb

/-- Every source Lipschitz constant yields the exact `M K ∫|f|/(R L)` error. -/
theorem abs_nyquistCriticalSource_error_le_of_source_lipschitz (m : ℕ) (f : C_c(ℝ, ℝ))
    (hne : f ≠ 0) {K : ℝ≥0} (hK : LipschitzWith K (f : ℝ → ℝ)) {L : ℝ} (hL : 0 < L) :
    |nyquistCriticalSourceResidual m f L - nyquistCriticalSourceSlope m f * L -
        nyquistCriticalFinitePart m| ≤
      (8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) *
        (K : ℝ) * (∫ u, |f u|) / (autocorr f 0 * L) := by
  have hb := abs_nyquistCriticalSource_error_le m f hne
    (lipschitzWith_nyquistNormalizedCorrelation_of_source f hne hK) hL
  change |nyquistCriticalSourceResidual m f L - nyquistCriticalSourceSlope m f * L -
        nyquistCriticalFinitePart m| ≤
      (8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) *
        ((K : ℝ) * (∫ u, |f u|) / autocorr f 0) / L at hb
  convert hb using 1
  ring

/-- The complete signed expansion for every fixed nonzero compact C² source and every positive scale. -/
theorem exists_nyquistCriticalSource_error_bound (m : ℕ) (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) :
    ∃ A : ℝ≥0, LipschitzWith A (nyquistNormalizedCorrelation f) ∧ ∀ L : ℝ, 0 < L →
      |nyquistCriticalSourceResidual m f L - nyquistCriticalSourceSlope m f * L -
          nyquistCriticalFinitePart m| ≤
        (8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) * (A : ℝ) / L := by
  obtain ⟨A, hA⟩ := exists_lipschitzWith_nyquistNormalizedCorrelation f hf hne
  exact ⟨A, hA, fun _ hL => abs_nyquistCriticalSource_error_le m f hne hA hL⟩

/-- After removing its exact linear term, every fixed source converges to the same finite part. -/
theorem tendsto_nyquistCriticalSourceResidual_sub_linear (m : ℕ) (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) :
    Tendsto (fun L => nyquistCriticalSourceResidual m f L - nyquistCriticalSourceSlope m f * L)
      atTop (𝓝 (nyquistCriticalFinitePart m)) := by
  obtain ⟨A, _, hA⟩ := exists_nyquistCriticalSource_error_bound m f hf hne
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm'
    (a := fun L => (8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) * (A : ℝ) / L)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [Real.norm_eq_abs]
    exact hA L hL
  · have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa only [div_eq_mul_inv, mul_zero] using
      hi.const_mul ((8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) * (A : ℝ))

/-- The linear coefficient is exactly the square of the ordinary source mean. -/
theorem tendsto_nyquistCriticalSourceResidual_div_scale (m : ℕ) (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) :
    Tendsto (fun L => nyquistCriticalSourceResidual m f L / L) atTop
      (𝓝 (nyquistCriticalSourceSlope m f)) := by
  have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hh := (tendsto_nyquistCriticalSourceResidual_sub_linear m f hf hne).mul hi
  simp only [mul_zero] at hh
  rw [← tendsto_sub_nhds_zero_iff]
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp [hL.ne']

theorem nyquistCriticalSourceSlope_eq_zero (m : ℕ) (f : C_c(ℝ, ℝ))
    (hmean : (∫ u, f u) = 0) : nyquistCriticalSourceSlope m f = 0 := by
  rw [nyquistCriticalSourceSlope, hmean, sq, zero_mul, mul_zero, zero_div]

theorem nyquistCriticalSourceSlope_pos (m : ℕ) (f : C_c(ℝ, ℝ))
    (hne : f ≠ 0) (hmean : (∫ u, f u) ≠ 0) : 0 < nyquistCriticalSourceSlope m f := by
  rw [nyquistCriticalSourceSlope, ← autocorr_zero_eq_integral_sq]
  exact div_pos (mul_pos (nyquistCriticalConstant_pos m) (sq_pos_of_ne_zero hmean))
    (mul_pos (by norm_num) (compactSource_mass_pos f hne))

/-- Ordinary zero source mean cancels linear escape and leaves the finite part itself. -/
theorem tendsto_nyquistCriticalSourceResidual_of_mean_zero (m : ℕ) (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) (hmean : (∫ u, f u) = 0) :
    Tendsto (nyquistCriticalSourceResidual m f) atTop (𝓝 (nyquistCriticalFinitePart m)) := by
  simpa only [nyquistCriticalSourceSlope_eq_zero m f hmean, zero_mul, sub_zero] using
    tendsto_nyquistCriticalSourceResidual_sub_linear m f hf hne

/-- Every fixed nonzero-mean source escapes linearly to positive infinity. -/
theorem tendsto_nyquistCriticalSourceResidual_atTop_of_mean_ne_zero (m : ℕ) (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) (hmean : (∫ u, f u) ≠ 0) :
    Tendsto (nyquistCriticalSourceResidual m f) atTop atTop := by
  have hlinear : Tendsto (fun L => nyquistCriticalSourceSlope m f * L) atTop atTop :=
    Tendsto.const_mul_atTop (nyquistCriticalSourceSlope_pos m f hne hmean) tendsto_id
  have hfinite := tendsto_nyquistCriticalSourceResidual_sub_linear m f hf hne
  apply tendsto_atTop.2
  intro b
  filter_upwards [hlinear.eventually_ge_atTop (b - (nyquistCriticalFinitePart m - 1)),
    hfinite.eventually (lt_mem_nhds (by linarith : nyquistCriticalFinitePart m - 1 <
      nyquistCriticalFinitePart m))] with L hlin hrem
  change nyquistCriticalFinitePart m - 1 <
    nyquistCriticalSourceResidual m f L - nyquistCriticalSourceSlope m f * L at hrem
  linarith only [hlin, hrem]

/-- The same actual stretched sources have vanishing normalized archimedean energy. -/
theorem tendsto_normalizedArchEnergy_broadSource (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) :
    Tendsto (fun L : ℝ => normalizedArchEnergy (sourceRescale f L⁻¹)) atTop (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := exists_sourceRescale_linear_energy_bound hf f.hasCompactSupport
    (compactSource_mass_pos f hne)
  apply squeeze_zero_norm' (a := fun L : ℝ => L⁻¹ * K)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hb := hK L⁻¹ (inv_pos.mpr hL)
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  · have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa only [zero_mul] using hi.mul_const K

end GaloisForLFunctions.BiScaleUncertainty
