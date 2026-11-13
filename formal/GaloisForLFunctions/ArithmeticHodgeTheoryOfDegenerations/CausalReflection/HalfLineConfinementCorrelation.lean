import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineEnergyGap

/-!
# Confinement controls correlation

The exponential square-mass excess controls the mass below every negative
cut. Cauchy–Schwarz then bounds positive-shift correlations by its square root.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- Excess of eighth-exponential square mass over ordinary square mass. -/
def criticalHalfLineExponentialDefect (F : ℝ → ℝ) : ℝ :=
  (∫ u, F u ^ 2 * Real.exp (-(8 * u))) - ∫ u, F u ^ 2

theorem CriticalHalfLineEnergyDomain.integrable_exponential_defect {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Integrable (fun u => F u ^ 2 * (Real.exp (-(8 * u)) - 1)) := by
  apply (hF.exponential.sub hF.sq).congr
  exact Eventually.of_forall fun u => by
    change F u ^ 2 * Real.exp (-(8 * u)) - F u ^ 2 = _
    ring

theorem CriticalHalfLineEnergyDomain.exponential_defect_integrand_nonneg {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (u : ℝ) :
    0 ≤ F u ^ 2 * (Real.exp (-(8 * u)) - 1) := by
  by_cases hu : 0 ≤ u
  · rw [hF.support u hu]
    simp only [zero_pow two_ne_zero, zero_mul, le_refl]
  · have he : 1 ≤ Real.exp (-(8 * u)) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      linarith only [lt_of_not_ge hu]
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr he)

theorem CriticalHalfLineEnergyDomain.integral_exponential_defect {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    (∫ u, F u ^ 2 * (Real.exp (-(8 * u)) - 1)) = criticalHalfLineExponentialDefect F := by
  simp_rw [mul_sub, mul_one]
  rw [integral_sub hF.exponential hF.sq]
  rfl

/-- Every nonzero half-line profile has strictly positive exponential excess. -/
theorem CriticalHalfLineEnergyDomain.exponential_defect_pos {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hm : 0 < ∫ u, F u ^ 2) :
    0 < criticalHalfLineExponentialDefect F := by
  have hn : 0 ≤ criticalHalfLineExponentialDefect F := by
    rw [← hF.integral_exponential_defect]
    exact integral_nonneg hF.exponential_defect_integrand_nonneg
  by_contra hnot
  have hz : criticalHalfLineExponentialDefect F = 0 := le_antisymm (le_of_not_gt hnot) hn
  have hi : (∫ u, F u ^ 2 * (Real.exp (-(8 * u)) - 1)) = 0 :=
    hF.integral_exponential_defect.trans hz
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall hF.exponential_defect_integrand_nonneg)
    hF.integrable_exponential_defect).mp hi
  have hzero : F =ᵐ[volume] 0 := by
    filter_upwards [hae] with u hu
    change F u = 0
    by_cases hupos : 0 ≤ u
    · exact hF.support u hupos
    · have he : 0 < Real.exp (-(8 * u)) - 1 := by
        apply sub_pos.mpr
        rw [← Real.exp_zero]
        apply Real.exp_lt_exp.mpr
        linarith only [lt_of_not_ge hupos]
      change F u ^ 2 * (Real.exp (-(8 * u)) - 1) = 0 at hu
      have hs := (mul_eq_zero.mp hu).resolve_right he.ne'
      nlinarith only [hs]
  have hm0 : (∫ u, F u ^ 2) = 0 := by
    calc
      _ = ∫ _u : ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hzero] with u hu
        change F u = 0 at hu
        simp only [hu, zero_pow two_ne_zero]
      _ = 0 := integral_zero _ _
  linarith only [hm, hm0]

private theorem nonnegative_setIntegral_le {f : ℝ → ℝ} (hf : Integrable f)
    (hn : ∀ u, 0 ≤ f u) (s : Set ℝ) : (∫ u in s, f u) ≤ ∫ u, f u := by
  have h := setIntegral_mono_set (s := s) (t := Set.univ) hf.integrableOn
    (Eventually.of_forall hn) (Eventually.of_forall fun u _ => mem_univ u)
  simpa only [Measure.restrict_univ] using h

/-- Shift overlap lies below the terminal cut, where confinement controls its mass. -/
theorem CriticalHalfLineEnergyDomain.correlation_sq_mul_exp_le {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {x : ℝ} (hx : 0 < x) :
    (∫ u, F u * F (u + x)) ^ 2 * (Real.exp (8 * x) - 1) ≤
      criticalHalfLineExponentialDefect F * (∫ u, F u ^ 2) := by
  have hshiftmeas : Measurable (fun u => F (u + x)) := by
    have hm := hF.meas
    fun_prop
  have hshift : Integrable (fun u => F (u + x) ^ 2) := hF.sq.comp_add_right x
  have hcoef : 0 < Real.exp (8 * x) - 1 := by
    apply sub_pos.mpr
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (mul_pos (by norm_num) hx)
  have hcorr : (∫ u, F u * F (u + x)) =
      ∫ u in Iic (-x), F u * F (u + x) := by
    have heq : (Iic (-x)).indicator (fun u => F u * F (u + x)) =
        fun u => F u * F (u + x) := by
      funext u
      by_cases hu : u ∈ Iic (-x)
      · exact indicator_of_mem hu _
      · rw [indicator_of_notMem hu, hF.support (u + x) (by
          have hh : -x < u := lt_of_not_ge hu
          linarith only [hh]), mul_zero]
    rw [← integral_indicator measurableSet_Iic, heq]
  have hc := HTGeometry.sq_integral_mul_le
    (μ := volume.restrict (Iic (-x))) hF.meas.aestronglyMeasurable
    hshiftmeas.aestronglyMeasurable hF.sq.integrableOn hshift.integrableOn
  have hshiftbound : (∫ u in Iic (-x), F (u + x) ^ 2) ≤ ∫ u, F u ^ 2 := by
    calc
      _ ≤ ∫ u, F (u + x) ^ 2 :=
        nonnegative_setIntegral_le hshift (fun u => sq_nonneg _) _
      _ = _ := integral_add_right_eq_self (fun u => F u ^ 2) x
  have htailnn : 0 ≤ ∫ u in Iic (-x), F u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hcs : (∫ u, F u * F (u + x)) ^ 2 ≤
      (∫ u in Iic (-x), F u ^ 2) * (∫ u, F u ^ 2) := by
    rw [hcorr]
    exact hc.trans (mul_le_mul_of_nonneg_left hshiftbound htailnn)
  have htail : (Real.exp (8 * x) - 1) * (∫ u in Iic (-x), F u ^ 2) ≤
      criticalHalfLineExponentialDefect F := by
    calc
      _ ≤ ∫ u in Iic (-x), F u ^ 2 * (Real.exp (-(8 * u)) - 1) := by
        rw [← integral_const_mul]
        apply setIntegral_mono_on (hF.sq.const_mul _).integrableOn
          hF.integrable_exponential_defect.integrableOn measurableSet_Iic
        intro u hu
        have he : Real.exp (8 * x) ≤ Real.exp (-(8 * u)) := by
          apply Real.exp_le_exp.mpr
          change u ≤ -x at hu
          linarith only [hu]
        calc
          _ = F u ^ 2 * (Real.exp (8 * x) - 1) := mul_comm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_sub_right he 1) (sq_nonneg _)
      _ ≤ ∫ u, F u ^ 2 * (Real.exp (-(8 * u)) - 1) :=
        nonnegative_setIntegral_le hF.integrable_exponential_defect
          hF.exponential_defect_integrand_nonneg _
      _ = _ := hF.integral_exponential_defect
  calc
    _ ≤ ((∫ u in Iic (-x), F u ^ 2) * (∫ u, F u ^ 2)) * (Real.exp (8 * x) - 1) :=
      mul_le_mul_of_nonneg_right hcs hcoef.le
    _ = ((Real.exp (8 * x) - 1) * (∫ u in Iic (-x), F u ^ 2)) * (∫ u, F u ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right htail (integral_nonneg fun u => sq_nonneg _)

/-- Unit-mass correlations decay beyond the scale of the exponential excess. -/
theorem CriticalHalfLineEnergyDomain.abs_correlation_le_sqrt_defect {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hm : (∫ u, F u ^ 2) = 1)
    {x : ℝ} (hx : 0 < x) :
    |∫ u, F u * F (u + x)| ≤ Real.sqrt (criticalHalfLineExponentialDefect F / (8 * x)) := by
  have h := hF.correlation_sq_mul_exp_le hx
  rw [hm, mul_one] at h
  have he : 8 * x ≤ Real.exp (8 * x) - 1 := by
    have hh := Real.add_one_le_exp (8 * x)
    linarith only [hh]
  have hsq : (∫ u, F u * F (u + x)) ^ 2 ≤ criticalHalfLineExponentialDefect F / (8 * x) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hx)).mpr
    exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans h
  exact Real.abs_le_sqrt hsq

#print axioms CriticalHalfLineEnergyDomain.abs_correlation_le_sqrt_defect

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
