import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.NegativeHalfLineExponentialBarrier
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFullGammaFormIsQuadraticOnItsIntegrableDomain

/-!
# Admissible positive levels above exponential barriers

Subtracting the barrier preserves finite Gamma energy. Taking the positive
part preserves it again, and pointwise domination by the original profile
recovers the stronger exponential mass required by the actual domain.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

/-- The positive part above a one-sided exponential barrier. -/
def exponentialBarrierPositiveLevel (β t : ℝ) (F : ℝ → ℝ) : ℝ → ℝ :=
  fun u => max (F u - t * negativeHalfLineExponentialBarrier β u) 0

theorem negativeHalfLineExponentialBarrier_nonneg (β u : ℝ) :
    0 ≤ negativeHalfLineExponentialBarrier β u := by
  by_cases hu : u ∈ Iic (0 : ℝ)
  · rw [negativeHalfLineExponentialBarrier, indicator_of_mem hu]
    exact (Real.exp_pos _).le
  · rw [negativeHalfLineExponentialBarrier, indicator_of_notMem hu]

theorem exponentialBarrierPositiveLevel_le_abs {t : ℝ} (ht : 0 ≤ t)
    (β : ℝ) (F : ℝ → ℝ) (u : ℝ) :
    0 ≤ exponentialBarrierPositiveLevel β t F u ∧
      exponentialBarrierPositiveLevel β t F u ≤ |F u| := by
  refine ⟨le_max_right _ _, max_le ?_ (abs_nonneg _)⟩
  exact (sub_le_self _ (mul_nonneg ht (negativeHalfLineExponentialBarrier_nonneg β u))).trans
    (le_abs_self _)

/-- Zero support makes the full positive exponential equivalent to its one-sided cutoff. -/
theorem CriticalHalfLineEnergyDomain.exponentialBarrierPositiveLevel_eq {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 0 ≤ t) (β u : ℝ) :
    exponentialBarrierPositiveLevel β t F u = max (F u - t * Real.exp (β * u)) 0 := by
  by_cases hu : u ∈ Iic (0 : ℝ)
  · rw [exponentialBarrierPositiveLevel, negativeHalfLineExponentialBarrier,
      indicator_of_mem hu]
  · have hu0 : 0 ≤ u := (lt_of_not_ge hu).le
    rw [exponentialBarrierPositiveLevel, negativeHalfLineExponentialBarrier,
      indicator_of_notMem hu, hF.support u hu0, mul_zero, sub_zero, max_self,
      zero_sub, max_eq_right (neg_nonpos.mpr (mul_nonneg ht (Real.exp_pos _).le))]

/-- Multiplication by the profile separates a nonnegative square and the barrier term. -/
theorem CriticalHalfLineEnergyDomain.mul_exponentialBarrierPositiveLevel {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 0 ≤ t) (β u : ℝ) :
    F u * exponentialBarrierPositiveLevel β t F u =
      exponentialBarrierPositiveLevel β t F u ^ 2 +
        t * Real.exp (β * u) * exponentialBarrierPositiveLevel β t F u := by
  rw [hF.exponentialBarrierPositiveLevel_eq ht]
  by_cases h : 0 ≤ F u - t * Real.exp (β * u)
  · rw [max_eq_left h]
    ring
  · rw [max_eq_right (lt_of_not_ge h).le]
    ring

theorem CriticalHalfLineEnergyDomain.mul_exponentialBarrierPositiveLevel_nonneg {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 0 ≤ t) (β u : ℝ) :
    0 ≤ F u * exponentialBarrierPositiveLevel β t F u := by
  rw [hF.mul_exponentialBarrierPositiveLevel ht]
  exact add_nonneg (sq_nonneg _) (mul_nonneg
    (mul_nonneg ht (Real.exp_pos _).le) (exponentialBarrierPositiveLevel_le_abs ht β F u).1)

/-- The mixed diagonal of a positive level is dominated by the original square. -/
theorem mul_exponentialBarrierPositiveLevel_le_sq {t : ℝ} (ht : 0 ≤ t)
    (β : ℝ) (F : ℝ → ℝ) (u : ℝ) :
    F u * exponentialBarrierPositiveLevel β t F u ≤ F u ^ 2 := by
  obtain ⟨hG0, hG⟩ := exponentialBarrierPositiveLevel_le_abs ht β F u
  calc
    _ ≤ |F u| * exponentialBarrierPositiveLevel β t F u :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hG0
    _ ≤ |F u| * |F u| := mul_le_mul_of_nonneg_left hG (abs_nonneg _)
    _ = _ := by rw [← sq, sq_abs]

/-- Every diagonal row of order at most eight is integrable against an exponential positive level. -/
theorem CriticalHalfLineEnergyDomain.integrable_mul_exponentialBarrierPositiveLevel
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {t c : ℝ}
    (ht : 0 ≤ t) (hc : c ≤ 8) (β : ℝ) :
    Integrable (fun u => F u * exponentialBarrierPositiveLevel β t F u * Real.exp (-(c * u))) := by
  have hGm : Measurable (exponentialBarrierPositiveLevel β t F) :=
    (hF.meas.sub (measurable_const.mul (measurable_negativeHalfLineExponentialBarrier β))).max
      measurable_const
  refine hF.exponential.mono' ((hF.meas.mul hGm).mul (by fun_prop)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (hF.mul_exponentialBarrierPositiveLevel_nonneg ht β u) (Real.exp_pos _).le)]
    by_cases hu : u ≤ 0
    · have he : Real.exp (-(c * u)) ≤ Real.exp (-(8 * u)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_nonneg (sub_nonneg.mpr hc) (neg_nonneg.mpr hu)]
      exact (mul_le_mul_of_nonneg_right (mul_exponentialBarrierPositiveLevel_le_sq ht β F u)
        (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))
    · rw [hF.support u (lt_of_not_ge hu).le]
      simp only [zero_mul, zero_pow two_ne_zero, le_refl]

/-- Positive-level exponential tests belong to the actual half-line energy domain. -/
theorem CriticalHalfLineEnergyDomain.exponentialBarrierPositiveLevel_mem {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    CriticalHalfLineEnergyDomain (exponentialBarrierPositiveLevel β t F) := by
  have hφm := measurable_negativeHalfLineExponentialBarrier β
  have hφ1 := integrable_negativeHalfLineExponentialBarrier hβ
  have hφ2 := memLp_negativeHalfLineExponentialBarrier hβ
  have hφsq : Integrable (fun u => negativeHalfLineExponentialBarrier β u ^ 2) := by
    rw [negativeHalfLineExponentialBarrier_sq]
    exact integrable_negativeHalfLineExponentialBarrier (mul_pos (by norm_num) hβ)
  let U : ℝ → ℝ := fun u => F u - t * negativeHalfLineExponentialBarrier β u
  have hUm : Measurable U := hF.meas.sub (measurable_const.mul hφm)
  have hU1 : Integrable U := hF.integrable.sub (hφ1.const_mul t)
  have hU2 : MemLp U 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hUm.aestronglyMeasurable).mpr
    have hc := hF.memLp_real.integrable_mul hφ2
    apply ((hF.sq.sub (hc.const_mul (2 * t))).add (hφsq.const_mul (t ^ 2))).congr
    exact Eventually.of_forall fun u => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, U, Real.norm_eq_abs, sq_abs]
      ring
  have hUγ : Integrable (fun r : ℝ => ‖paperFT (cx U) r‖ ^ 2 * EF.gammaBracket r) := by
    have hh := integrable_gamma_add_const_mul hF.integrable hφ1 hF.gamma
      (integrable_gammaBracket_negativeHalfLineExponentialBarrier hβ) (-t)
    simpa only [U, neg_mul, sub_eq_add_neg] using hh
  have hpos : LipschitzWith 1 (fun x : ℝ => max x 0) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_max_sub_max_le_abs x y 0
  have hGm : Measurable (exponentialBarrierPositiveLevel β t F) :=
    hUm.max measurable_const
  have hb := exponentialBarrierPositiveLevel_le_abs ht β F
  have hsq (u : ℝ) : exponentialBarrierPositiveLevel β t F u ^ 2 ≤ F u ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr (hb u).2)
      (add_nonneg (abs_nonneg _) (hb u).1)
    nlinarith only [hh, sq_abs (F u)]
  refine ⟨hGm, ?_, ?_, ?_, ?_, ?_⟩
  · refine hF.integrable.norm.mono' hGm.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hb u).1, Real.norm_eq_abs]
    exact (hb u).2
  · refine hF.sq.mono' (hGm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (exponentialBarrierPositiveLevel β t F u))]
    exact hsq u
  · refine hF.exponential.mono' ((hGm.pow_const 2).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (sq_nonneg (exponentialBarrierPositiveLevel β t F u)) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right (hsq u) (Real.exp_pos _).le
  · intro u hu
    rw [exponentialBarrierPositiveLevel, hF.support u hu, zero_sub]
    exact max_eq_right (neg_nonpos.mpr (mul_nonneg ht
      (negativeHalfLineExponentialBarrier_nonneg β u)))
  · exact integrable_gammaBracket_comp_contraction hUm hU1 hU2 hUγ hpos (by norm_num)

#print axioms CriticalHalfLineEnergyDomain.exponentialBarrierPositiveLevel_mem
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
