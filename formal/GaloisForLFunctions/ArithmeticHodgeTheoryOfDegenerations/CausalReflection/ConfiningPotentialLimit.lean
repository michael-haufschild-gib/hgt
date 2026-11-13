import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicHalfLineDomain
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineConfinementTail
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity
import GaloisForLFunctions.FiniteFreeProbability.JensenSaddleError

/-!
# Linearization of the confining potential

An available exponential moment dominates the difference quotients of the
exponential potential. Dominated convergence identifies their integral
limit with eight times the physical first moment.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri


theorem tendsto_confiningExponentialSlope (t : ℝ) :
    Tendsto (fun a : ℝ => a * (Real.exp (8 * t / a) - 1)) atTop (𝓝 (8 * t)) := by
  have ht : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_inv_atTop_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    simpa only [mem_compl_iff, mem_singleton_iff] using inv_ne_zero ha.ne'
  apply ((HilbertMetric.tendsto_exp_mul_sub_one_div (8 * t)).comp ht).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  change (Real.exp (a⁻¹ * (8 * t)) - 1) / a⁻¹ = _
  have he : a⁻¹ * (8 * t) = 8 * t / a := by ring
  rw [div_inv_eq_mul, he, mul_comm]

/-- Half of an available exponential rate dominates the linearized confinement potential. -/
theorem confiningExponentialSlope_bound {β a t : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hA : 16 / β ≤ a) (ht : 0 ≤ t) :
    0 ≤ a * (Real.exp (8 * t / a) - 1) ∧
      a * (Real.exp (8 * t / a) - 1) ≤ (16 / β) * Real.exp (β * t) := by
  have hv : 0 ≤ 8 * t / a := by positivity
  have hratio : 8 / a ≤ β / 2 := by
    have h := (div_le_iff₀ hβ).mp hA
    apply (div_le_iff₀ ha).mpr
    nlinarith only [h]
  have hvt : 8 * t / a ≤ β * t / 2 := by
    have h := mul_le_mul_of_nonneg_right hratio ht
    convert h using 1 <;> ring
  refine ⟨mul_nonneg ha.le (sub_nonneg.mpr (Real.one_le_exp hv)), ?_⟩
  have hlinear : 8 * t ≤ (16 / β) * Real.exp (β * t / 2) := by
    have he := Real.add_one_le_exp (β * t / 2)
    have hh : 8 * t * β ≤ 16 * Real.exp (β * t / 2) := by nlinarith only [he]
    have hh' := (le_div_iff₀ hβ).mpr hh
    convert hh' using 1 <;> ring
  calc
    _ ≤ a * ((8 * t / a) * Real.exp (8 * t / a)) :=
      mul_le_mul_of_nonneg_left FiniteFreeProbability.exp_sub_one_le_mul_exp ha.le
    _ = (8 * t) * Real.exp (8 * t / a) := by field_simp [ha.ne']
    _ ≤ (8 * t) * Real.exp (β * t / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hvt) (by positivity)
    _ ≤ ((16 / β) * Real.exp (β * t / 2)) * Real.exp (β * t / 2) :=
      mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring

/-- Fixed exponentially controlled profiles have the linear limiting potential. -/
theorem SoftLogarithmicHalfLineDomain.tendsto_potentialIntegral {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) :
    Tendsto (fun a : ℝ => ∫ u, a * (Real.exp (8 * (-u) / a) - 1) * F u ^ 2)
      atTop (𝓝 (8 * ∫ u, (-u) * F u ^ 2)) := by
  obtain ⟨β, hβ, hi⟩ := hF.exponential
  have hdom : Integrable (fun u => (16 / β) * (F u ^ 2 * Real.exp (-(β * u)))) :=
    hi.const_mul _
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := atTop)
    (F := fun (a : ℝ) u => a * (Real.exp (8 * (-u) / a) - 1) * F u ^ 2)
    (f := fun u => (8 * (-u)) * F u ^ 2)
    (fun u => (16 / β) * (F u ^ 2 * Real.exp (-(β * u))))
    (Eventually.of_forall fun a => by
      have hm := hF.meas
      exact (by fun_prop : Measurable (fun u =>
        a * (Real.exp (8 * (-u) / a) - 1) * F u ^ 2)).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (max 1 (16 / β))] with a ha
      have ha0 : 0 < a := zero_lt_one.trans_le ((le_max_left _ _).trans ha)
      exact Eventually.of_forall fun u => by
        by_cases hu : 0 ≤ u
        · simp only [hF.support u hu, zero_pow two_ne_zero, mul_zero, zero_mul, norm_zero, le_refl]
        · have hb := confiningExponentialSlope_bound hβ ha0
            ((le_max_right _ _).trans ha) (neg_nonneg.mpr (lt_of_not_ge hu).le)
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (sq_nonneg _))]
          have hh := mul_le_mul_of_nonneg_right hb.2 (sq_nonneg (F u))
          simpa only [mul_neg, neg_mul, mul_assoc, mul_left_comm, mul_comm] using hh)
    hdom
    (Eventually.of_forall fun u => (tendsto_confiningExponentialSlope (-u)).mul_const (F u ^ 2))
  have he : (∫ u, (8 * (-u)) * F u ^ 2) = 8 * ∫ u, (-u) * F u ^ 2 := by
    simp only [mul_assoc]
    exact integral_const_mul _ _
  rwa [he] at h

/-- Compression linearizes the exponential excess for every fixed logarithmic-domain trial. -/
theorem SoftLogarithmicHalfLineDomain.tendsto_scaled_exponentialDefect {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) :
    Tendsto (fun a : ℝ => a * criticalHalfLineExponentialDefect (unitaryRealDilation a F))
      atTop (𝓝 (8 * criticalHalfLineFirstMoment F)) := by
  apply hF.tendsto_potentialIntegral.congr'
  filter_upwards [hF.eventually_actual_dilation, eventually_gt_atTop (0 : ℝ)] with a hd ha
  change (∫ u, a * (Real.exp (8 * (-u) / a) - 1) * F u ^ 2) =
    a * criticalHalfLineExponentialDefect (unitaryRealDilation a F)
  rw [← hd.integral_exponential_defect]
  have he : (∫ u, unitaryRealDilation a F u ^ 2 * (Real.exp (-(8 * u)) - 1)) =
      ∫ u, (Real.exp (-(8 * (u / a))) - 1) * F u ^ 2 := by
    calc
      _ = ∫ u, (Real.exp (-(8 * u)) - 1) * unitaryRealDilation a F u ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun u => mul_comm _ _
      _ = _ := integral_weighted_sq_unitaryRealDilation ha F (fun u => Real.exp (-(8 * u)) - 1)
  rw [he, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    have he : 8 * (-u) / a = -(8 * (u / a)) := by ring
    rw [he]
    ring

#print axioms SoftLogarithmicHalfLineDomain.tendsto_scaled_exponentialDefect
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
