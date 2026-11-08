import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarFarGammaRowsHaveUniformMeans
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.SymmetricExponentialMeans

/-!
# The scalar polar Gamma means have one limit

Symmetric logarithmic quadrature recovers the near and far singular integrals.
Their common finite part, together with the harmonic center constant, is
exactly the polar scalar `-aφ log(2π)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- The scalar mean of the separated Gamma annulus in logarithmic coordinates. -/
def polarFarMean (T w : ℝ) : ℝ :=
  (∫ t in (-T)..T, polarFarClampedKernel tiltedUnitSpline t * Real.exp (w * t / 2)) -
    ∫ t in (-2 : ℝ)..2, polarFarClampedKernel tiltedUnitSpline t * Real.exp (w * t / 2)

lemma continuous_polarFarClampedKernel : Continuous (polarFarClampedKernel tiltedUnitSpline) := by
  obtain ⟨C, hC, _, hL⟩ := exists_polarFarClampedKernel_bounds
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  have hlip : LipschitzWith (Real.toNNReal C) (polarFarClampedKernel tiltedUnitSpline) := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    simpa only [Real.dist_eq, Real.coe_toNNReal _ hC] using hL s t
  exact hlip.continuous

lemma continuous_polarFarMean (T : ℝ) : Continuous (polarFarMean T) :=
  (continuous_exponential_mean continuous_polarFarClampedKernel T).sub
    (continuous_exponential_mean continuous_polarFarClampedKernel 2)

/-- On a fixed annulus, the scalar far mean changes at most linearly with atom width. -/
theorem exists_abs_polarFarMean_sub_zero_le {T : ℝ} (hT : 2 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : ℝ}, |w| * T ≤ 1 / 2 →
      |polarFarMean T w - polarFarMean T 0| ≤ C * |w| := by
  obtain ⟨A, hA, hbound, _⟩ := exists_polarFarClampedKernel_bounds
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  refine ⟨2 * A * (T ^ 2 + 4), by positivity, fun {w} hw => ?_⟩
  have hbig := abs_exponential_mean_sub_le (by linarith only [hT] : 0 < T) hA
    continuous_polarFarClampedKernel.continuousOn (fun t _ => hbound t) hw
  have hw2 : |w| * 2 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hT (abs_nonneg w)).trans hw
  have hsmall := abs_exponential_mean_sub_le (by norm_num : (0 : ℝ) < 2) hA
    continuous_polarFarClampedKernel.continuousOn (fun t _ => hbound t) hw2
  unfold polarFarMean
  simp only [zero_mul, zero_div, Real.exp_zero, mul_one]
  have hid (a b c d : ℝ) : (a - b) - (c - d) = (a - c) - (b - d) := by ring
  rw [hid]
  exact ((abs_sub _ _).trans (add_le_add hbig hsmall)).trans_eq (by ring)


/-- At zero width the logarithmic annulus mean is twice the positive far integral. -/
theorem polarFarMean_zero {T : ℝ} (hT : 2 ≤ T) :
    polarFarMean T 0 = 2 * ∫ s in (2 : ℝ)..T, crossSingular tiltedUnitSpline (1 / s) := by
  let K := polarFarClampedKernel tiltedUnitSpline
  have hc : Continuous K := continuous_polarFarClampedKernel
  have heven : ∀ t, K (-t) = K t := by intro t; simp only [K, polarFarClampedKernel, abs_neg]
  have hbig := integral_symmetric_even_eq_two_mul (hc.intervalIntegrable (-T) 0)
    (hc.intervalIntegrable 0 T) heven
  have hsmall := integral_symmetric_even_eq_two_mul (hc.intervalIntegrable (-2) 0)
    (hc.intervalIntegrable 0 2) heven
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 2) (hc.intervalIntegrable 2 T)
  have hcross : (∫ s in (2 : ℝ)..T, K s) = ∫ s in (2 : ℝ)..T,
      crossSingular tiltedUnitSpline (1 / s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT] at hs
    simp only [K, polarFarClampedKernel, abs_of_nonneg (by linarith only [hs.1] : 0 ≤ s),
      max_eq_right hs.1]
  unfold polarFarMean
  simp only [zero_mul, zero_div, Real.exp_zero, mul_one]
  change (∫ s in (-T)..T, K s) - ∫ s in (-2 : ℝ)..2, K s = _
  rw [hbig, hsmall, ← hsplit, hcross]
  ring

/-- The far scalar mean approaches its finite part with reciprocal annulus error. -/
theorem abs_polarFarMean_zero_sub_le {T : ℝ} (hT : 2 ≤ T) :
    |polarFarMean T 0 - 2 * farCrossFinitePart tiltedUnitSpline| ≤ 4 / T := by
  rw [polarFarMean_zero hT, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (mul_le_mul_of_nonneg_left
    (abs_integral_crossSingular_inv_sub_le contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos hT) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

/-- The even near kernel is bounded and Lipschitz on its full collar. -/
lemma polarNearKernel_bounds :
    ∃ A L : ℝ, 0 ≤ A ∧ 0 ≤ L ∧
    (∀ t ∈ Icc (-2 : ℝ) 2, |nearKernel tiltedUnitSpline |t| / (∫ u, tiltedUnitSpline u ^ 2)| ≤ A) ∧
    ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      |nearKernel tiltedUnitSpline |s| / (∫ u, tiltedUnitSpline u ^ 2) -
        nearKernel tiltedUnitSpline |t| / (∫ u, tiltedUnitSpline u ^ 2)| ≤ L * |s - t| := by
  have hI := integral_tiltedUnitSpline_sq_pos
  obtain ⟨A, L, hL, hA, hLip⟩ := exists_nearKernel_bounds contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (by constructor <;> norm_num))
  have hmem (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) 2) : |t| ∈ Icc (0 : ℝ) 2 :=
    ⟨abs_nonneg _, abs_le.mpr ht⟩
  refine ⟨A / (∫ u, tiltedUnitSpline u ^ 2), L / (∫ u, tiltedUnitSpline u ^ 2),
    by positivity, by positivity, ?_, ?_⟩
  · intro t ht
    rw [abs_div, abs_of_pos hI]
    exact div_le_div_of_nonneg_right (hA _ (hmem t ht)) hI.le
  · intro s hs t ht
    rw [← sub_div, abs_div, abs_of_pos hI]
    have hh := (hLip _ (hmem s hs) _ (hmem t ht)).trans
      (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le s t) hL)
    exact (div_le_div_of_nonneg_right hh hI.le).trans_eq (by ring)

/-- The near scalar mean changes by at most a fixed multiple of the atom width. -/
theorem exists_abs_polarNearJointMean_sub_zero_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : ℝ}, |w| ≤ 1 / 4 →
      |polarNearJointMean w - polarNearJointMean 0| ≤ C * |w| := by
  obtain ⟨A, L, hA, _, hbound, hLip⟩ := polarNearKernel_bounds
  let K : ℝ → ℝ := fun t => nearKernel tiltedUnitSpline |t| / (∫ u, tiltedUnitSpline u ^ 2)
  have hcont : ContinuousOn K (Icc (-2 : ℝ) 2) := continuousOn_of_abs_sub_le hLip
  refine ⟨8 * A, by positivity, fun {w} hw => ?_⟩
  have hb := abs_exponential_mean_sub_le (by norm_num : (0 : ℝ) < 2) hA hcont hbound
    (by linarith only [hw] : |w| * 2 ≤ 1 / 2)
  unfold polarNearJointMean polarNearSmoothMean
  simp only [zero_mul, zero_div, Real.exp_zero, mul_one]
  have he : ∀ a b d : ℝ, (a + d) - (b + d) = a - b := by intros; ring
  rw [he]
  exact hb.trans_eq (by ring)

/-- The zero-width near mean is the symmetric near-kernel integral. -/
theorem polarNearSmoothMean_zero :
    polarNearSmoothMean 0 = (2 / (∫ u, tiltedUnitSpline u ^ 2)) *
      ∫ s in (0 : ℝ)..2, nearKernel tiltedUnitSpline s := by
  obtain ⟨A, L, _, _, _, hLip⟩ := polarNearKernel_bounds
  let K : ℝ → ℝ := fun t => nearKernel tiltedUnitSpline |t| / (∫ u, tiltedUnitSpline u ^ 2)
  have hc : ContinuousOn K (Icc (-2 : ℝ) 2) := continuousOn_of_abs_sub_le hLip
  have hi : IntervalIntegrable K volume (-2) 2 :=
    hc.intervalIntegrable_of_Icc (by norm_num : (-2 : ℝ) ≤ 2)
  have hneg : IntervalIntegrable K volume (-2) 0 := hi.mono_set (by
    rw [uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 0), uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have hpos : IntervalIntegrable K volume 0 2 := hi.mono_set (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2), uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have heven : ∀ t, K (-t) = K t := by intro t; simp only [K, abs_neg]
  have hh := integral_symmetric_even_eq_two_mul hneg hpos heven
  unfold polarNearSmoothMean
  simp only [zero_mul, zero_div, Real.exp_zero, mul_one]
  change (∫ t in (-2 : ℝ)..2, K t) = _
  rw [hh]
  have hp : (∫ t in (0 : ℝ)..2, K t) =
      (∫ t in (0 : ℝ)..2, nearKernel tiltedUnitSpline t) / (∫ u, tiltedUnitSpline u ^ 2) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    simp only [K, abs_of_nonneg ht.1]
  rw [hp]
  ring

/-- Near and far Gamma means, including the harmonic collar constant, have the exact polar
finite part dictated by the completed archimedean factor. -/
theorem polarNearJointMean_sub_farFinitePart :
    polarNearJointMean 0 - 2 * farCrossFinitePart tiltedUnitSpline =
      -((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) * Real.log (2 * Real.pi) := by
  have hf : Tendsto (fun T : ℝ => polarFarMean T 0 - 2 * farCrossFinitePart tiltedUnitSpline)
      atTop (𝓝 0) := by
    have hb : Tendsto (fun T : ℝ => 4 / T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero_norm' _ hb
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs] using abs_polarFarMean_zero_sub_le hT
  have hf' : Tendsto (fun T : ℝ => polarFarMean T 0) atTop
      (𝓝 (2 * farCrossFinitePart tiltedUnitSpline)) := by
    simpa only [zero_add, sub_add_cancel] using hf.add_const (2 * farCrossFinitePart tiltedUnitSpline)
  have hlim := (tendsto_const_nhds (x := polarNearSmoothMean 0)).sub hf'
  have hknown := tendsto_joint_near_far_Gamma_integral
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  have heq := tendsto_nhds_unique hlim (hknown.congr' (by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    rw [polarFarMean_zero hT, polarNearSmoothMean_zero]))
  have hlog : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * Real.pi ≠ 0)]
    congr 1
    ring
  rw [hlog] at heq
  unfold polarNearJointMean
  linarith only [heq]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
