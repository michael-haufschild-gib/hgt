import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineConfinementCorrelation

/-!
# Exponential tails and the first moment under confinement

The exponential excess controls the weighted mass beyond every terminal
cut and dominates eight times the physical first moment.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- Physical first moment measured from the terminal boundary. -/
def criticalHalfLineFirstMoment (F : ℝ → ℝ) : ℝ := ∫ u, (-u) * F u ^ 2

/-- The weighted tail is paid for by the exponential excess. -/
theorem CriticalHalfLineEnergyDomain.exponential_tail_mul_le_defect {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) :
    (1 - Real.exp (-(8 * x))) * (∫ u in Iic (-x), F u ^ 2 * Real.exp (-(8 * u))) ≤
      criticalHalfLineExponentialDefect F := by
  have htail : (∫ u in Iic (-x), F u ^ 2 * (Real.exp (-(8 * u)) - 1)) ≤
      criticalHalfLineExponentialDefect F := by
    have h := setIntegral_mono_set (s := Iic (-x)) (t := Set.univ)
      hF.integrable_exponential_defect.integrableOn
      (Eventually.of_forall hF.exponential_defect_integrand_nonneg)
      (Eventually.of_forall fun u _ => mem_univ u)
    simpa only [Measure.restrict_univ, hF.integral_exponential_defect] using h
  apply le_trans _ htail
  rw [← integral_const_mul]
  apply setIntegral_mono_on (hF.exponential.const_mul _).integrableOn
    hF.integrable_exponential_defect.integrableOn measurableSet_Iic
  intro u hu
  have he : 1 ≤ Real.exp (-(8 * x)) * Real.exp (-(8 * u)) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    change u ≤ -x at hu
    linarith only [hu]
  have hh : (1 - Real.exp (-(8 * x))) * Real.exp (-(8 * u)) ≤
      Real.exp (-(8 * u)) - 1 := by nlinarith only [he]
  calc
    _ = F u ^ 2 * ((1 - Real.exp (-(8 * x))) * Real.exp (-(8 * u))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (sq_nonneg _)

theorem CriticalHalfLineEnergyDomain.exponential_tail_le_defect {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {x : ℝ} (hx : 0 < x) :
    (∫ u in Iic (-x), F u ^ 2 * Real.exp (-(8 * u))) ≤
      criticalHalfLineExponentialDefect F / (1 - Real.exp (-(8 * x))) := by
  have hc : 0 < 1 - Real.exp (-(8 * x)) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    linarith only [hx]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using hF.exponential_tail_mul_le_defect x

theorem CriticalHalfLineEnergyDomain.firstMoment_integrand_nonneg {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (u : ℝ) : 0 ≤ (-u) * F u ^ 2 := by
  by_cases hu : 0 ≤ u
  · rw [hF.support u hu]
    simp only [zero_pow two_ne_zero, mul_zero, le_refl]
  · exact mul_nonneg (neg_nonneg.mpr (lt_of_not_ge hu).le) (sq_nonneg _)

private theorem firstMoment_integrand_le (F : ℝ → ℝ) (u : ℝ) :
    8 * ((-u) * F u ^ 2) ≤ F u ^ 2 * (Real.exp (-(8 * u)) - 1) := by
  have h : -(8 * u) ≤ Real.exp (-(8 * u)) - 1 := by
    linarith only [Real.add_one_le_exp (-(8 * u))]
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (F u))
  nlinarith only [hh]

theorem CriticalHalfLineEnergyDomain.integrable_firstMoment {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : Integrable (fun u => (-u) * F u ^ 2) := by
  apply (hF.integrable_exponential_defect.div_const 8).mono'
  · have hm : Measurable (fun u => (-u) * F u ^ 2) := by
      have h := hF.meas
      fun_prop
    exact hm.aestronglyMeasurable
  · exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF.firstMoment_integrand_nonneg u)]
      have h := firstMoment_integrand_le F u
      linarith only [h]

/-- Exponential confinement dominates its linearized physical potential. -/
theorem CriticalHalfLineEnergyDomain.eight_mul_firstMoment_le_defect {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    8 * criticalHalfLineFirstMoment F ≤ criticalHalfLineExponentialDefect F := by
  have h := integral_mono (hF.integrable_firstMoment.const_mul 8)
    hF.integrable_exponential_defect (firstMoment_integrand_le F)
  rw [integral_const_mul, hF.integral_exponential_defect] at h
  exact h

#print axioms CriticalHalfLineEnergyDomain.exponential_tail_le_defect
#print axioms CriticalHalfLineEnergyDomain.eight_mul_firstMoment_le_defect

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
