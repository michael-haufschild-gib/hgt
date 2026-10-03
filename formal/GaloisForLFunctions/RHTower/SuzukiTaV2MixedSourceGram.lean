import GaloisForLFunctions.RHTower.SuzukiTaV2PrescribedEnergySource

open MeasureTheory Set Filter
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Exact mixed polar-source Gram integral, including zero total slope. -/
theorem inner_ccmPolarApertureVector_eq_exp_integral
    (a : SuzukiPositiveAperture) (s t : ℝ) :
    inner ℂ (ccmPolarApertureVector a s) (ccmPolarApertureVector a t) =
      ((∫ x in (-a.1)..a.1, Real.exp ((s + t) * x) : ℝ) : ℂ) := by
  change inner ℂ (ccmPolarL2Vector a s) (ccmPolarL2Vector a t) = _
  rw [L2.inner_def]
  calc
    _ = ∫ x in centralInterval a.1, (Real.exp ((s + t) * x) : ℂ) := by
      rw [← integral_indicator (measurableSet_centralInterval a.1)]
      apply integral_congr_ae
      filter_upwards [ccmPolarL2Vector_coeFn a s, ccmPolarL2Vector_coeFn a t]
        with x hx hy
      rw [hx, hy]
      by_cases hmem : x ∈ centralInterval a.1
      · rw [indicator_of_mem hmem, indicator_of_mem hmem, indicator_of_mem hmem]
        simp only [ccmPolarProfile, RCLike.inner_apply, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        congr 2
        ring
      · simp [indicator_of_notMem hmem]
    _ = ((∫ x in centralInterval a.1, Real.exp ((s + t) * x) : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = _ := by
      congr 1
      rw [intervalIntegral.integral_of_le (by linarith [a.property])]
      unfold centralInterval
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Closed mixed Gram law when the sum of source slopes is nonzero. -/
theorem inner_ccmPolarApertureVector_eq_exp_quotient
    (a : SuzukiPositiveAperture) (s t : ℝ) (h : s + t ≠ 0) :
    inner ℂ (ccmPolarApertureVector a s) (ccmPolarApertureVector a t) =
      (((Real.exp ((s + t) * a.1) - Real.exp (-(s + t) * a.1)) / (s + t) : ℝ) : ℂ) := by
  rw [inner_ccmPolarApertureVector_eq_exp_integral,
    intervalIntegral.integral_comp_mul_left Real.exp h, integral_exp]
  congr 1
  simp only [smul_eq_mul, mul_neg, neg_mul]
  ring

/-- Source comparison with the audited half-pole eliminates any aperture-length
loss for every slope at least one half. -/
theorem norm_ccmPolarApertureVector_le_exp_of_half_le
    (a : SuzukiPositiveAperture) (s : ℝ) (hs : 1 / 2 ≤ s) :
    ‖ccmPolarApertureVector a s‖ ≤ Real.exp (s * a.1) := by
  have hpoint : ∀ᵐ x : ℝ, ‖(ccmPolarL2Vector a s : ℝ → ℂ) x‖ ≤
      Real.exp ((s - 1 / 2) * a.1) * ‖(ccmPolarL2Vector a (1 / 2) : ℝ → ℂ) x‖ := by
    filter_upwards [ccmPolarL2Vector_coeFn a s, ccmPolarL2Vector_coeFn a (1 / 2)] with x hx hy
    rw [hx, hy]
    by_cases hmem : x ∈ centralInterval a.1
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      simp only [ccmPolarProfile, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hmem.2 (sub_nonneg.mpr hs)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      simp
  have hn := Lp.norm_le_mul_norm_of_ae_le_mul hpoint
  have he : (Real.exp (a.1 / 2)) ^ 2 = Real.exp a.1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hhalf : ‖ccmPolarApertureVector a (1 / 2)‖ ≤ Real.exp (a.1 / 2) := by
    have hsq := norm_sq_ccmPolarApertureVector_half a
    rw [Real.sinh_eq] at hsq
    nlinarith [Real.exp_pos (-a.1), Real.exp_pos (a.1 / 2)]
  change ‖ccmPolarApertureVector a s‖ ≤
    Real.exp ((s - 1 / 2) * a.1) * ‖ccmPolarApertureVector a (1 / 2)‖ at hn
  calc
    _ ≤ Real.exp ((s - 1 / 2) * a.1) * ‖ccmPolarApertureVector a (1 / 2)‖ := hn
    _ ≤ Real.exp ((s - 1 / 2) * a.1) * Real.exp (a.1 / 2) :=
      mul_le_mul_of_nonneg_left hhalf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem norm_ccmPolarApertureVector_neg_le_exp_of_half_le
    (a : SuzukiPositiveAperture) (s : ℝ) (hs : 1 / 2 ≤ s) :
    ‖ccmPolarApertureVector a (-s)‖ ≤ Real.exp (s * a.1) := by
  change ‖ccmPolarL2Vector a (-s)‖ ≤ _
  rw [← l2Reflection_ccmPolarL2Vector a s]
  change ‖l2ReflectionIsometry (ccmPolarL2Vector a s)‖ ≤ _
  rw [l2ReflectionIsometry.norm_map]
  exact norm_ccmPolarApertureVector_le_exp_of_half_le a s hs

end RHTower
end
