import GaloisForLFunctions.HTGeometry.EntireParameterSpatialDerivative
import GaloisForLFunctions.RHTower.PaperThetaParameterTraces
import GaloisForLFunctions.RHTower.PaperThetaCutSourceEquation

/-! # Strong spatial equations for the actual theta parameter jets

The decreasing native variation budget pays differentiation of every Cauchy
coefficient. The resulting spatial equation retains the predecessor jet and
the actual endpoint trace; no joint regularity premise is introduced.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped ContDiff

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

theorem continuous_sourceLogDerivative : Continuous sourceLogDerivative := by
  have hr : ContDiff ℝ ∞ thetaSource.normalized :=
    contDiff_thetaCuspFullSource.div_const _
  have hc : ContDiff ℝ ∞ (fun x : ℝ => (thetaSource.normalized x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  exact hc.continuous_deriv (by simp) |>.div hc.continuous
    (fun x => by exact_mod_cast (thetaSource.normalized_pos x).ne')

private def spatialRHS (z : ℂ) (x : ℝ) : ℂ :=
  (-I) * (z * flatQuotient z x) + (-sourceLogDerivative x) * (1 + flatQuotient z x)

private theorem hasDerivAt_flatQuotient_rhs (z : ℂ) (x : ℝ) :
    HasDerivAt (flatQuotient z) (spatialRHS z x) x := by
  have he : deriv (flatQuotient z) x = spatialRHS z x := by
    dsimp only [spatialRHS]
    linear_combination flatQuotient_source_equation z x
  rw [← he]
  exact (differentiable_flatQuotient z x).hasDerivAt

private theorem differentiable_spatialRHS_parameter (x : ℝ) :
    Differentiable ℂ (fun z => spatialRHS z x) := by
  exact ((differentiable_id.mul (differentiable_flatQuotient_parameter x)).const_mul _).add
    (((differentiable_const (1 : ℂ)).add (differentiable_flatQuotient_parameter x)).const_mul _)

private theorem spatialRHS_parameter_circle_bound (z : ℂ) (a : ℝ) :
    ∃ C : ℝ, ∀ w ∈ Metric.sphere z 1, ∀ x ∈ Metric.ball a 1, ‖spatialRHS w x‖ ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (a-1) (a+1)) continuous_sourceLogDerivative.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (sourceLogDerivative a)).trans
    (hM a ⟨by linarith, by linarith⟩)
  let B := parameterVariationBudget z (a-1)
  have hB : 0 ≤ B := parameterVariationBudget_nonneg z (a-1)
  refine ⟨(‖z‖+1)*(B+1)+M*B, ?_⟩
  intro w hw x hx
  have hdist : |x-a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hx
  have hx' : x ∈ Icc (a-1) (a+1) := by
    constructor <;> linarith [abs_lt.mp hdist |>.1, abs_lt.mp hdist |>.2]
  have hq1 : ‖1+flatQuotient w x‖ ≤ B := by
    rw [add_comm]
    exact (flatQuotient_add_one_parameter_circle z x hw).trans
      (parameterVariationBudget_antitone z hx'.1)
  have hq : ‖flatQuotient w x‖ ≤ B+1 := by
    have hh := norm_sub_le (1+flatQuotient w x) (1 : ℂ)
    have hh' : ‖flatQuotient w x‖ ≤ ‖1+flatQuotient w x‖+1 := by
      simpa only [add_sub_cancel_left, norm_one] using hh
    linarith
  have hw' : ‖w‖ ≤ ‖z‖+1 := by
    have ht := norm_add_le (w-z) z
    have hd : ‖w-z‖ = 1 := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
    rw [sub_add_cancel, hd] at ht
    simpa only [add_comm] using ht
  calc
    ‖spatialRHS w x‖ ≤ ‖(-I)*(w*flatQuotient w x)‖ +
        ‖(-sourceLogDerivative x)*(1+flatQuotient w x)‖ := norm_add_le _ _
    _ = ‖w‖*‖flatQuotient w x‖ + ‖sourceLogDerivative x‖*‖1+flatQuotient w x‖ := by
      simp only [norm_mul, norm_neg, norm_I, one_mul]
    _ ≤ (‖z‖+1)*(B+1)+M*B := add_le_add
      (mul_le_mul hw' hq (norm_nonneg _) (by positivity))
      (mul_le_mul (hM x hx') hq1 (norm_nonneg _) hM0)

/-- Parameter differentiation commutes with the actual strong spatial derivative. -/
private theorem hasDerivAt_flatParameterJet (n : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (flatParameterJet n z)
      (iteratedDeriv n (fun w => spatialRHS w x) z) x :=
  hasDerivAt_entireParameterJet flatQuotient spatialRHS x z n
    differentiable_flatQuotient_parameter (differentiable_spatialRHS_parameter x)
    (fun w _ y _ => hasDerivAt_flatQuotient_rhs w y)
    (spatialRHS_parameter_circle_bound z x)

theorem differentiable_flatParameterJet (n : ℕ) (z : ℂ) :
    Differentiable ℝ (flatParameterJet n z) :=
  fun x => (hasDerivAt_flatParameterJet n z x).differentiableAt

/-- The full predecessor term survives strong differentiation at every order. -/
theorem flatParameterJet_succ_source_equation (n : ℕ) (z : ℂ) (x : ℝ) :
    deriv (flatParameterJet (n+1) z) x + I*z*flatParameterJet (n+1) z x +
      I*((n:ℂ)+1)*flatParameterJet n z x + sourceLogDerivative x*flatParameterJet (n+1) z x = 0 := by
  rw [(hasDerivAt_flatParameterJet (n+1) z x).deriv]
  have hf := differentiable_flatQuotient_parameter x
  have h₁ : AnalyticAt ℂ (fun w => -I * (w * flatQuotient w x)) z :=
    ((differentiable_id.mul hf).const_mul (-I)).analyticAt z
  have h₂ : AnalyticAt ℂ (fun w => -sourceLogDerivative x * (1 + flatQuotient w x)) z :=
    (((differentiable_const (1 : ℂ)).add hf).const_mul (-sourceLogDerivative x)).analyticAt z
  simp only [spatialRHS]
  rw [iteratedDeriv_fun_add h₁.contDiffAt h₂.contDiffAt,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_const_add (Nat.succ_pos n), entire_iteratedDeriv_id_mul hf]
  simp only [flatParameterJet]
  ring

end RHTower.PaperThetaEndpoint
