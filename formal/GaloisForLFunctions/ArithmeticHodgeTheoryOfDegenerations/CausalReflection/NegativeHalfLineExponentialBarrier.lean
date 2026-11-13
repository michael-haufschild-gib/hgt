import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineGammaContractions
import GaloisForLFunctions.RHTower.CHMDThetaRelativeGraph

/-!
# Exponential barriers have finite Gamma energy

A one-sided exponential has an exact translation defect bounded by the
displacement. The finite first Lévy moment therefore places the barrier in
the full Gamma domain, despite its jump at the endpoint.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open ArithmeticCastelnuovoSeveri ArchimedeanAnomaly

/-- The positive exponential barrier, cut at the terminal endpoint. -/
def negativeHalfLineExponentialBarrier (β : ℝ) : ℝ → ℝ :=
  (Iic (0 : ℝ)).indicator (fun u => Real.exp (β * u))

theorem measurable_negativeHalfLineExponentialBarrier (β : ℝ) :
    Measurable (negativeHalfLineExponentialBarrier β) :=
  (by fun_prop : Measurable (fun u : ℝ => Real.exp (β * u))).indicator measurableSet_Iic

theorem integrable_negativeHalfLineExponentialBarrier {β : ℝ} (hβ : 0 < β) :
    Integrable (negativeHalfLineExponentialBarrier β) :=
  (integrableOn_exp_mul_Iic hβ 0).integrable_indicator measurableSet_Iic

theorem negativeHalfLineExponentialBarrier_sq (β : ℝ) :
    (fun u => negativeHalfLineExponentialBarrier β u ^ 2) =
      negativeHalfLineExponentialBarrier (2 * β) := by
  funext u
  by_cases hu : u ∈ Iic (0 : ℝ)
  · simp only [negativeHalfLineExponentialBarrier, indicator_of_mem hu]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  · simp only [negativeHalfLineExponentialBarrier, indicator_of_notMem hu,
      zero_pow (by decide : 2 ≠ 0)]

theorem integral_sq_negativeHalfLineExponentialBarrier {β : ℝ} (hβ : 0 < β) :
    (∫ u, negativeHalfLineExponentialBarrier β u ^ 2) = 1 / (2 * β) := by
  rw [negativeHalfLineExponentialBarrier_sq, negativeHalfLineExponentialBarrier,
    integral_indicator measurableSet_Iic, integral_exp_mul_Iic (mul_pos (by norm_num) hβ) 0]
  rw [mul_zero, Real.exp_zero]

theorem memLp_negativeHalfLineExponentialBarrier {β : ℝ} (hβ : 0 < β) :
    MemLp (negativeHalfLineExponentialBarrier β) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_negativeHalfLineExponentialBarrier β).aestronglyMeasurable).mpr
  simp only [Real.norm_eq_abs, sq_abs]
  rw [negativeHalfLineExponentialBarrier_sq]
  exact integrable_negativeHalfLineExponentialBarrier (mul_pos (by norm_num) hβ)

private theorem exponentialBarrier_product {β h : ℝ} (hh : 0 ≤ h) :
    (fun u => negativeHalfLineExponentialBarrier β u *
      negativeHalfLineExponentialBarrier β (u + h)) =
      (Iic (-h)).indicator (fun u => Real.exp (β * h) * Real.exp ((2 * β) * u)) := by
  funext u
  by_cases hu : u ∈ Iic (-h)
  · have hu0 : u ∈ Iic (0 : ℝ) := by change u ≤ 0; linarith only [hu, hh]
    have huh : u + h ∈ Iic (0 : ℝ) := by change u + h ≤ 0; linarith only [hu]
    simp only [negativeHalfLineExponentialBarrier, indicator_of_mem hu,
      indicator_of_mem hu0, indicator_of_mem huh]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · have huh : u + h ∉ Iic (0 : ℝ) := by
      intro hzero
      apply hu
      change u ≤ -h
      linarith only [hzero]
    simp only [negativeHalfLineExponentialBarrier, indicator_of_notMem hu,
      indicator_of_notMem huh, mul_zero]

/-- The barrier's positive-lag autocorrelation is exponential. -/
theorem autocorr_negativeHalfLineExponentialBarrier {β h : ℝ}
    (hβ : 0 < β) (hh : 0 ≤ h) :
    autocorr (negativeHalfLineExponentialBarrier β) h = Real.exp (-(β * h)) / (2 * β) := by
  rw [autocorr, exponentialBarrier_product hh, integral_indicator measurableSet_Iic,
    integral_const_mul, integral_exp_mul_Iic (mul_pos (by norm_num) hβ) (-h),
    ← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The squared translation defect is bounded by its displacement, independently of the rate. -/
theorem translation_defect_negativeHalfLineExponentialBarrier {β h : ℝ}
    (hβ : 0 < β) (hh : 0 ≤ h) :
    (∫ u, (negativeHalfLineExponentialBarrier β u -
      negativeHalfLineExponentialBarrier β (u + h)) ^ 2) =
      (1 - Real.exp (-(β * h))) / β ∧
    (∫ u, (negativeHalfLineExponentialBarrier β u -
      negativeHalfLineExponentialBarrier β (u + h)) ^ 2) ≤ h := by
  have he : (∫ u, (negativeHalfLineExponentialBarrier β u -
      negativeHalfLineExponentialBarrier β (u + h)) ^ 2) =
      (1 - Real.exp (-(β * h))) / β := by
    rw [AutocorrelationKrein.integral_sub_shift_sq (memLp_negativeHalfLineExponentialBarrier hβ),
      AutocorrelationKrein.autocorr_zero_eq, integral_sq_negativeHalfLineExponentialBarrier hβ,
      autocorr_negativeHalfLineExponentialBarrier hβ hh]
    field_simp [hβ.ne']
    ring
  refine ⟨he, ?_⟩
  rw [he]
  apply (div_le_iff₀ hβ).mpr
  have hh := Real.add_one_le_exp (-(β * h))
  nlinarith only [hh]

/-- The barrier's endpoint jump has finite physical Gamma energy. -/
theorem integrableOn_levyIntegrand_negativeHalfLineExponentialBarrier {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun h : ℝ => archLevyDensity h *
      ∫ u, (negativeHalfLineExponentialBarrier β u -
        negativeHalfLineExponentialBarrier β (u + h)) ^ 2) (Ioi 0) := by
  have hm := measurable_negativeHalfLineExponentialBarrier β
  have hj : Measurable (fun p : ℝ × ℝ => (negativeHalfLineExponentialBarrier β p.2 -
      negativeHalfLineExponentialBarrier β (p.2 + p.1)) ^ 2) := by fun_prop
  refine CHMDDoobGraph.integrableOn_mul_archLevyDensity.mono'
    (measurable_archLevyDensity.aestronglyMeasurable.mul
      hj.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos hh).le
    (integral_nonneg fun u => sq_nonneg _))]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (translation_defect_negativeHalfLineExponentialBarrier hβ hh.le).2 (archLevyDensity_pos hh).le

theorem integrable_gammaBracket_negativeHalfLineExponentialBarrier {β : ℝ} (hβ : 0 < β) :
    Integrable (fun r : ℝ => ‖paperFT (cx (negativeHalfLineExponentialBarrier β)) r‖ ^ 2 *
      EF.gammaBracket r) :=
  integrable_gammaBracket_of_levyIntegrand
    (integrable_negativeHalfLineExponentialBarrier hβ)
    (memLp_negativeHalfLineExponentialBarrier hβ)
    (integrableOn_levyIntegrand_negativeHalfLineExponentialBarrier hβ)

#print axioms translation_defect_negativeHalfLineExponentialBarrier
#print axioms integrable_gammaBracket_negativeHalfLineExponentialBarrier
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
