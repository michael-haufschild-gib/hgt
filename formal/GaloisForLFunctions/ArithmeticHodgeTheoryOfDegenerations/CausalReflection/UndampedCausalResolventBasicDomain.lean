import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ComplexHalfLinePoleDomain
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalLaplaceReflection

/-!
# Actual integrability of an undamped causal resolvent

A positive exponential weight dominates the unweighted norm on the negative
half-line. At a Laplace zero the undamped resolvent has exactly this support,
so its weighted square bound also supplies ordinary L² and L¹ admission.
-/

noncomputable section
open MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- On the negative half-line, a positive exponential square weight dominates L². -/
theorem memLp_two_of_weighted_negativeHalfLine {x : ℝ} (hx : 0 ≤ x)
    {f : ℝ → ℂ} (hm : Measurable f)
    (hw : MemLp (causalLaplaceWeighted x f) 2 volume)
    (hs : ∀ u, 0 ≤ u → f u = 0) : MemLp f 2 volume := by
  have hi := (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply hi.mono' (hm.aestronglyMeasurable.norm.pow 2)
  refine Eventually.of_forall fun u => ?_
  change ‖‖f u‖ ^ 2‖ ≤ ‖causalLaplaceWeighted x f u‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_sq_causalLaplaceWeighted]
  by_cases hu : 0 ≤ u
  · rw [hs u hu, norm_zero]
    norm_num
  · have hneg : 2 * Real.pi * x * u ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hx) (le_of_not_ge hu)
    have he : 1 ≤ Real.exp (-(2 * Real.pi * x * u)) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonneg.mpr hneg)
    calc
      _ = ‖f u‖ ^ 2 * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left he (sq_nonneg _)

/-- Cancellation of an imaginary-axis Laplace zero admits its undamped resolvent in L¹∩L². -/
theorem undampedCausalConvolution_memLp_and_integrable (b : ℝ)
    {f : ℝ → ℂ} (hm : Measurable f)
    (hw : MemLp (causalLaplaceWeighted (4 / Real.pi) f) 2 volume)
    (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f (modulatedLaplaceRate 0 b) = 0) :
    MemLp (modulatedCausalConvolution 0 b f) 2 volume ∧
      Integrable (modulatedCausalConvolution 0 b f) := by
  have hKm := measurable_modulatedCausalConvolution 0 b hm
  have hKw := memLp_weighted_modulatedCausalConvolution
    (a := 0) (x := 4 / Real.pi) (by positivity) b hw
  have hKs := modulatedCausalConvolution_support_of_laplace_zero 0 b hs hz
  have hK2 := memLp_two_of_weighted_negativeHalfLine
    (x := 4 / Real.pi) (by positivity) hKm hKw hKs
  refine ⟨hK2, ?_⟩
  have hi := integrable_complexLaplaceWeighted_of_halfLine_memLp
    (q := 0) (by norm_num) hK2 hKw hKs
  change Integrable (fun u : ℝ => Complex.exp ((0 : ℂ) * (u : ℂ)) *
    modulatedCausalConvolution 0 b f u) at hi
  simpa only [zero_mul, Complex.exp_zero, one_mul] using hi

end GaloisForLFunctions.HTGeometry
