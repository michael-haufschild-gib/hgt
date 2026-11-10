import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveMeasureHamburgerRigidity

/-!
# Mellin transforms of positive convolution exponentials

A prime-power measure on `(1,∞)` generates its integer measure by
multiplicative convolution exponential. Its Mellin transform is the
ordinary exponential of the prime-power transform, for every complex
argument at which the absolute Mellin moment is finite.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped ENNReal
open GaloisForLFunctions.ArithmeticPositiveDuality

namespace GaloisForLFunctions.EulerFETransportTheory

/-- The complex Mellin character is measurable, including its assigned value at zero. -/
theorem measurable_measureMellin (s : ℂ) :
    Measurable (fun u : ℝ => (u : ℂ) ^ (-s)) := by
  refine measurable_of_continuousOn_compl_singleton (0 : ℝ) ?_
  intro u hu
  exact (Complex.continuousAt_ofReal_cpow_const u (-s)
    (Or.inr (by simpa only [mem_compl_iff, mem_singleton_iff] using hu))).continuousWithinAt

/-- Absolute Mellin integrability is precisely the real moment bound. -/
theorem integrable_measureMellin_of_moment {P : Measure ℝ}
    (hP : P (Iio 1) = 0) {s : ℂ}
    (hmom : Integrable (fun u : ℝ => u ^ (-s.re)) P) :
    Integrable (fun u : ℝ => (u : ℂ) ^ (-s)) P := by
  refine hmom.mono' (measurable_measureMellin s).aestronglyMeasurable ?_
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hP] with u hu
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le zero_lt_one hu), Complex.neg_re]

/-- Mellin transforms multiply under multiplicative convolution. -/
theorem measureDirichlet_mconv {P Q : Measure ℝ} [SFinite P] [SFinite Q]
    (hP : P (Iio 1) = 0) (hQ : Q (Iio 1) = 0) (s : ℂ) :
    measureDirichlet (P ∗ₘ Q) s = measureDirichlet P s * measureDirichlet Q s := by
  rw [measureDirichlet, Measure.mconv,
    integral_map measurable_mul.aemeasurable (measurable_measureMellin s).aestronglyMeasurable]
  have hprod : ∀ᵐ z : ℝ × ℝ ∂P.prod Q, 1 ≤ z.1 ∧ 1 ≤ z.2 := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      ((measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_const measurable_snd))).mpr
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hP] with u hu
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hQ] with v hv
    exact ⟨hu, hv⟩
  calc
    (∫ z : ℝ × ℝ, ((z.1 * z.2 : ℝ) : ℂ) ^ (-s) ∂P.prod Q) =
        ∫ z : ℝ × ℝ, (z.1 : ℂ) ^ (-s) * (z.2 : ℂ) ^ (-s) ∂P.prod Q := by
      apply integral_congr_ae
      filter_upwards [hprod] with z hz
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
        (zero_le_one.trans hz.1) (zero_le_one.trans hz.2)]
    _ = _ := integral_prod_mul (fun u : ℝ => (u : ℂ) ^ (-s))
      (fun u : ℝ => (u : ℂ) ^ (-s))

/-- Every convolution power is supported on `[1,∞)`. -/
theorem mulConvPow_Iio_one {P : Measure ℝ} [SFinite P]
    (hP : P (Iic 1) = 0) (m : ℕ) : mulConvPow P m (Iio 1) = 0 := by
  cases m with
  | zero => simp [mulConvPow]
  | succ m =>
    exact measure_mono_null Iio_subset_Iic_self
      (mulConvPow_succ_Iic_one_eq_zero hP m)

/-- The Mellin transform of a convolution power is the corresponding power. -/
theorem measureDirichlet_mulConvPow {P : Measure ℝ} [SFinite P]
    (hP : P (Iic 1) = 0) (s : ℂ) (m : ℕ) :
    measureDirichlet (mulConvPow P m) s = measureDirichlet P s ^ m := by
  induction m with
  | zero => simp [mulConvPow, measureDirichlet]
  | succ m ih =>
    rw [mulConvPow, measureDirichlet_mconv
      (measure_mono_null Iio_subset_Iic_self hP) (mulConvPow_Iio_one hP m), ih, pow_succ']

/-- The complex Euler identity for every positive prime-power measure with finite absolute moment. -/
theorem measureDirichlet_beurlingIntegerMeasure {P : Measure ℝ} [SFinite P]
    (hP : P (Iic 1) = 0) {s : ℂ}
    (hmom : Integrable (fun u : ℝ => u ^ (-s.re)) P) :
    measureDirichlet (beurlingIntegerMeasure P) s = Complex.exp (measureDirichlet P s) := by
  have hi := integrable_measureMellin_of_moment
    (beurlingIntegerMeasure_Iio_one_eq_zero hP)
    (integrable_rpow_neg_beurlingIntegerMeasure hP hmom)
  rw [measureDirichlet, beurlingIntegerMeasure, integral_sum_measure hi]
  simp_rw [integral_smul_measure]
  change (∑' m : ℕ, ((m.factorial : ℝ≥0∞)⁻¹).toReal •
    measureDirichlet (mulConvPow P m) s) = _
  simp_rw [measureDirichlet_mulConvPow hP s]
  have hterm (m : ℕ) :
      ((m.factorial : ℝ≥0∞)⁻¹).toReal • measureDirichlet P s ^ m =
        measureDirichlet P s ^ m / (m.factorial : ℂ) := by
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_inv_mul]
  simp_rw [hterm]
  rw [Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq

#print axioms measureDirichlet_beurlingIntegerMeasure

end GaloisForLFunctions.EulerFETransportTheory
