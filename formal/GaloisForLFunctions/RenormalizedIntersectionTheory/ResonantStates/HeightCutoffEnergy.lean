import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CoreSourceSquare
import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CutoffGramKernel

/-!
# Exact height-weighted energy added by a cusp cutoff

A cutoff increment is the constant Fourier mode on its height band. Complete
horocycles make it orthogonal to the lower truncation even after multiplication
by a bounded continuous function of height.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- The actual increment is supported on a complete-horocycle band. -/
theorem truncatedLineModel_cutoff_difference (u : ℂ) {Y Z : ℝ} (hYZ : Y ≤ Z) (z : ℍ) :
    truncatedLineModel u Z z - truncatedLineModel u Y z =
      if Y < z.im ∧ z.im ≤ Z then d4BMCompletedEisensteinCuspConstantPart .scalar u z.im else 0 := by
  unfold truncatedLineModel
  by_cases hy : Y < z.im
  · by_cases hz : Z < z.im
    · simp only [hy, hz, not_le_of_gt hz, and_false, if_true, if_false]
      ring
    · simp only [hy, hz, le_of_not_gt hz, and_self, if_true, if_false]
      ring
  · have hz : ¬ Z < z.im := fun hz => hy (lt_of_le_of_lt hYZ hz)
    simp only [hy, hz, false_and, if_false]
    ring

private theorem weighted_cutoff_product_integrable (g : ℝ → ℝ) (hg : Measurable g)
    {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) (u v : ℂ) {Y Z : ℝ} (hY : 1 ≤ Y) (hZ : 1 ≤ Z) :
    IntegrableOn (fun z : ℍ => (g z.im : ℂ) * truncatedLineModel u Y z *
      truncatedLineModel v Z z) fd := by
  have hm := ((Complex.measurable_ofReal.comp (hg.comp UpperHalfPlane.continuous_im.measurable)).mul
    (measurable_truncatedLineModel u Y)).mul (measurable_truncatedLineModel v Z)
  refine Measure.integrableOn_of_bounded volume_fd_ne_top hm.aestronglyMeasurable
    (M := M * truncBound' u Y * truncBound' v Z) ?_
  refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Eventually.of_forall fun z hz => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real]
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have h₁ := mul_le_mul (hM z.im) (norm_truncatedLineModel_le_truncBound' u hY hz)
    (norm_nonneg _) hM0
  exact mul_le_mul h₁ (norm_truncatedLineModel_le_truncBound' v hZ hz)
    (norm_nonneg _) ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans h₁)

/-- Bounded measurable height tests preserve square integrability. -/
theorem height_weighted_norm_integrable (g : ℝ → ℝ) (hg : Measurable g)
    {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) (u : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z : ℍ => g z.im * ‖truncatedLineModel u Y z‖ ^ 2) fd := by
  have hi := (weighted_cutoff_product_integrable g hg hM u ((starRingEnd ℂ) u) hY hY).re
  simpa only [← truncatedLineModel_conj, mul_assoc, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re] using hi

theorem cutoff_norm_sq_integrable (u : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z : ℍ => ‖truncatedLineModel u Y z‖ ^ 2) fd := by
  simpa only [one_mul] using height_weighted_norm_integrable (fun _ => 1) measurable_const
    (M := 1) (fun _ => by norm_num) u hY

private theorem weighted_cutoff_pairing_of_le (g : ℝ → ℝ) (hg : Continuous g)
    {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) (u v : ℂ) {Y Z : ℝ}
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) :
    (∫ z in fd, (g z.im : ℂ) * truncatedLineModel u Y z * truncatedLineModel v Z z) =
      ∫ z in fd, (g z.im : ℂ) * truncatedLineModel u Y z * truncatedLineModel v Y z := by
  have hdiff : (fun z : ℍ =>
      (g z.im : ℂ) * truncatedLineModel u Y z * truncatedLineModel v Z z -
        (g z.im : ℂ) * truncatedLineModel u Y z * truncatedLineModel v Y z) =
      (fun z => if Y < z.im ∧ z.im ≤ Z then
        ((g z.im : ℂ) * d4BMCompletedEisensteinCuspConstantPart .scalar v z.im) *
          d4BMCompletedEisensteinCuspTailPart .scalar u z.re z.im else 0) := by
    funext z
    unfold truncatedLineModel eisensteinLineModel d4BMCompletedEisensteinCuspLeg
    by_cases hy : Y < z.im
    · by_cases hz : Z < z.im
      · simp only [hy, hz, not_le_of_gt hz, and_false, if_true, if_false]
        ring
      · simp only [hy, hz, le_of_not_gt hz, and_self, if_true, if_false]
        ring
    · have hz : ¬ Z < z.im := fun hz => hy (lt_of_le_of_lt hYZ hz)
      simp only [hy, hz, false_and, if_false]
      ring
  have hz : (∫ z in fd,
      (g z.im : ℂ) * truncatedLineModel u Y z * truncatedLineModel v Z z -
        (g z.im : ℂ) * truncatedLineModel u Y z * truncatedLineModel v Y z) = 0 := by
    rw [hdiff]
    exact setIntegral_band_mul_tail_eq_zero u hY _
      ((Complex.continuous_ofReal.comp hg).continuousOn.mul
        (continuousOn_cuspConstantPart_height v (by linarith)))
  rw [integral_sub (weighted_cutoff_product_integrable g hg.measurable hM u v hY (hY.trans hYZ))
    (weighted_cutoff_product_integrable g hg.measurable hM u v hY hY)] at hz
  exact sub_eq_zero.mp hz

/-- Height weighting preserves the orthogonal energy increment. -/
theorem height_weighted_energy_increment (g : ℝ → ℝ) (hg : Continuous g)
    {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) (u : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ z in fd, g z.im * ‖truncatedLineModel u Y z‖ ^ 2) =
      (∫ z in fd, g z.im * ‖truncatedLineModel u 1 z‖ ^ 2) +
        ∫ z in fd, if 1 < z.im ∧ z.im ≤ Y then
          g z.im * ‖d4BMCompletedEisensteinCuspConstantPart .scalar u z.im‖ ^ 2 else 0 := by
  let P : ℝ → ℝ → ℍ → ℂ := fun A B z =>
    (g z.im : ℂ) * truncatedLineModel u A z * truncatedLineModel ((starRingEnd ℂ) u) B z
  have hi (A B : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) : IntegrableOn (P A B) fd :=
    weighted_cutoff_product_integrable g hg.measurable hM u ((starRingEnd ℂ) u) hA hB
  have hc₁ : (∫ z in fd, P 1 Y z) = ∫ z in fd, P 1 1 z :=
    weighted_cutoff_pairing_of_le g hg hM u ((starRingEnd ℂ) u) (by norm_num) hY
  have hc₂ : (∫ z in fd, P Y 1 z) = ∫ z in fd, P 1 1 z := by
    have h := weighted_cutoff_pairing_of_le g hg hM ((starRingEnd ℂ) u) u (by norm_num) hY
    convert h using 1 <;> congr 1 <;> funext z <;> dsimp [P] <;> ring
  have hdiag (A : ℝ) : (∫ z in fd, P A A z) =
      ((∫ z in fd, g z.im * ‖truncatedLineModel u A z‖ ^ 2 : ℝ) : ℂ) := by
    simp only [P, ← truncatedLineModel_conj, mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, integral_complex_ofReal]
  have hd : (fun z : ℍ => P Y Y z - P Y 1 z - P 1 Y z + P 1 1 z) =
      fun z => ((if 1 < z.im ∧ z.im ≤ Y then
        g z.im * ‖d4BMCompletedEisensteinCuspConstantPart .scalar u z.im‖ ^ 2 else 0 : ℝ) : ℂ) := by
    funext z
    have he : P Y Y z - P Y 1 z - P 1 Y z + P 1 1 z =
        (g z.im : ℂ) * ((‖truncatedLineModel u Y z - truncatedLineModel u 1 z‖ ^ 2 : ℝ) : ℂ) := by
      dsimp [P]
      simp only [← truncatedLineModel_conj, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
        map_sub]
      ring
    rw [he, truncatedLineModel_cutoff_difference u hY z]
    split_ifs <;> simp only [Complex.ofReal_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, Complex.ofReal_zero]
  have hdint := congrArg (fun F : ℍ → ℂ => ∫ z in fd, F z) hd
  rw [integral_add ((hi Y Y hY hY).sub (hi Y 1 hY (by norm_num)) |>.sub (hi 1 Y (by norm_num) hY))
      (hi 1 1 (by norm_num) (by norm_num)),
    integral_sub ((hi Y Y hY hY).sub (hi Y 1 hY (by norm_num))) (hi 1 Y (by norm_num) hY),
    integral_sub (hi Y Y hY hY) (hi Y 1 hY (by norm_num)), hc₁, hc₂,
    hdiag Y, hdiag 1, integral_complex_ofReal] at hdint
  apply Complex.ofReal_injective
  push_cast
  linear_combination hdint

/-- At a resonance, the height-band increment is the explicit outgoing power density. -/
theorem resonant_height_weighted_energy (g : ℝ → ℝ) (hg : Continuous g)
    {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) {u : ℂ} (hAu : msA u = 0)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ z in fd, g z.im * ‖truncatedLineModel u Y z‖ ^ 2) =
      (∫ z in fd, g z.im * ‖truncatedLineModel u 1 z‖ ^ 2) +
        ‖msB u‖ ^ 2 * ∫ y in Ioc 1 Y, g y * y ^ (-2 * u.re - 1) := by
  rw [height_weighted_energy_increment g hg hM u hY]
  congr 1
  have he : (∫ z in fd, if 1 < z.im ∧ z.im ≤ Y then
      g z.im * ‖d4BMCompletedEisensteinCuspConstantPart .scalar u z.im‖ ^ 2 else 0 : ℝ) =
      ∫ z in fd, if 1 < z.im ∧ z.im ≤ Y then
        g z.im * (‖msB u‖ ^ 2 * z.im ^ (1 - 2 * u.re)) else 0 := by
    apply setIntegral_congr_fun isClosed_fd.measurableSet
    intro z hz
    split_ifs with hy
    · rw [cuspConstantPart_eq_msAB, hAu, zero_mul, zero_add, norm_mul, mul_pow,
        Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos, rpow_half_sub_sq z.im_pos]
    · rfl
  rw [he]
  have hh : ContinuousOn (fun y : ℝ => ((g y * (‖msB u‖ ^ 2 * y ^ (1 - 2 * u.re)) : ℝ) : ℂ))
      (Icc 1 Y) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    exact hg.continuousOn.mul (continuousOn_const.mul
      (continuousOn_id.rpow_const (fun y hy => Or.inl (by linarith [hy.1]))))
  have hint := setIntegral_fd_height (Y₂ := Y) (by norm_num : (1 : ℝ) ≤ 1) _ hh
  have hfun : (fun z : ℍ => if 1 < z.im ∧ z.im ≤ Y then
      ((g z.im * (‖msB u‖ ^ 2 * z.im ^ (1 - 2 * u.re)) : ℝ) : ℂ) else 0) =
      fun z => ((if 1 < z.im ∧ z.im ≤ Y then
        g z.im * (‖msB u‖ ^ 2 * z.im ^ (1 - 2 * u.re)) else 0 : ℝ) : ℂ) := by
    funext z; split_ifs <;> rfl
  rw [hfun, integral_complex_ofReal] at hint
  have hr : (∫ y in Ioc 1 Y,
      ((g y * (‖msB u‖ ^ 2 * y ^ (1 - 2 * u.re)) : ℝ) : ℂ) / (y : ℂ) ^ 2) =
      ((‖msB u‖ ^ 2 * ∫ y in Ioc 1 Y, g y * y ^ (-2 * u.re - 1) : ℝ) : ℂ) := by
    calc
      _ = ∫ y in Ioc 1 Y, ((‖msB u‖ ^ 2 * (g y * y ^ (-2 * u.re - 1)) : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
        have hy0 : 0 < y := lt_trans (by norm_num) hy.1
        rw [← Complex.ofReal_pow, ← Complex.ofReal_div]
        apply congrArg Complex.ofReal
        rw [← Real.rpow_two, mul_div_assoc, mul_div_assoc, ← Real.rpow_sub hy0]
        congr 1 <;> ring
      _ = _ := by rw [integral_complex_ofReal, integral_const_mul]
  exact Complex.ofReal_injective (hint.trans hr)

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
