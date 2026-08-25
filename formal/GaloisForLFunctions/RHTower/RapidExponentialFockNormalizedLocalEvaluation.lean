import GaloisForLFunctions.RHTower.PolynomialFockLocalEvaluation
import GaloisForLFunctions.RHTower.RapidExponentialFockLocalEvaluation
import GaloisForLFunctions.RHTower.RapidExponentialMomentFockKernelLower

/-!
# Normalized local evaluation for the rapid exponential Fock carrier

The local weighted mean estimate and explicit diagonal-kernel lower bound combine into a local
bound for normalized reproducing-kernel coefficients.  Its polynomial loss is recorded exactly.
-/

open MeasureTheory Set Metric
open scoped Real

namespace RHTower

noncomputable section

/-- Explicit loss in normalized local evaluation. -/
def rapidExponentialFockLocalEvaluationFactor (a x : ℝ) : ℝ :=
  Real.exp 2 /
    ((2 * rapidExponentialFockTangentCurvature a x) *
      rapidExponentialFockLocalRadius a x ^ 2)

theorem rapidExponentialFockLocalEvaluationFactor_pos
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    0 < rapidExponentialFockLocalEvaluationFactor a x := by
  unfold rapidExponentialFockLocalEvaluationFactor
  have hc := rapidExponentialFockTangentCurvature_pos ha hx
  have hr := rapidExponentialFockLocalRadius_pos (x := x) ha
  positivity

/-- A normalized rapid-moment Fock evaluation is controlled by one explicit local ball. -/
theorem normSq_inner_normalizedRapidExponentialMomentFockKernel_le_localIntegral
    {a x : ℝ} (ha : 0 < a) (hx : 1 / 2 ≤ x) (f : MomentFock) :
    ‖inner ℂ (normalizedMomentFockKernel
        (rapidExponentialMomentFockData a ha) (x : ℂ)) f‖ ^ 2 ≤
      rapidExponentialFockLocalEvaluationFactor a x *
        ∫ z in Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x),
          rapidExponentialMomentFockWeightedNormSq a ha f z := by
  let d : MomentFockData := rapidExponentialMomentFockData a ha
  let A : ℝ := ‖inner ℂ (normalizedMomentFockKernel d (x : ℂ)) f‖ ^ 2
  let K : ℝ := ‖momentFockKernel d (x : ℂ)‖ ^ 2
  let E : ℝ := Real.exp (2 * rapidExponentialFockPotential a x)
  let C : ℝ := Real.exp 2
  let q : ℝ := 2 * rapidExponentialFockTangentCurvature a x
  let R : ℝ := rapidExponentialFockLocalRadius a x ^ 2
  let I : ℝ := ∫ z in Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x),
    rapidExponentialMomentFockWeightedNormSq a ha f z
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hx0 : 0 ≤ x := by linarith
  have hq : 0 < q := by
    dsimp [q]
    exact mul_pos (by norm_num) (rapidExponentialFockTangentCurvature_pos ha hx0)
  have hR : 0 < R := by
    dsimp [R]
    exact sq_pos_of_pos (rapidExponentialFockLocalRadius_pos ha)
  have hqR : 0 < q * R := mul_pos hq hR
  have hI : 0 ≤ I := by
    dsimp [I]
    apply MeasureTheory.integral_nonneg
    intro z
    exact rapidExponentialMomentFockWeightedNormSq_nonneg a ha f z
  have hid : A * K =
      ‖rapidExponentialMomentFockEvaluation a ha (x : ℂ) f‖ ^ 2 := by
    dsimp [A, K, d]
    exact normSq_inner_normalizedMomentFockKernel_mul_kernelNormSq _ _ _
  have hmean := rapidExponentialFock_local_weighted_mean ha hx
    (rapidExponentialMomentFockFunction a ha f)
    (differentiable_rapidExponentialMomentFockFunction a ha f)
  have hmean' :
      Real.pi * R * ‖rapidExponentialMomentFockEvaluation a ha (x : ℂ) f‖ ^ 2 ≤
        E * C * I := by
    rw [rapidExponentialMomentFockFunction_eq_evaluation] at hmean
    have hdensity : (fun z =>
        ‖rapidExponentialMomentFockFunction a ha f z‖ ^ 2 *
          Real.exp (-2 * rapidExponentialFockPotential a ‖z‖)) =
        rapidExponentialMomentFockWeightedNormSq a ha f := by
      funext z
      rfl
    rw [hdensity] at hmean
    simpa [E, C, R, I, Real.exp_add] using hmean
  have hkernel := normSq_rapidExponentialMomentFockKernel_lower ha hx0
  have hden : E * q * R ≤ Real.pi * R * K := by
    calc
      E * q * R = Real.pi * R * (E * (q / Real.pi)) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ Real.pi * R * K := by
        gcongr
  have hleft : E * q * R * A ≤ Real.pi * R * K * A :=
    mul_le_mul_of_nonneg_right hden hA
  have hright : Real.pi * R * K * A ≤ E * C * I := by
    calc
      Real.pi * R * K * A =
          Real.pi * R * (A * K) := by ring
      _ = Real.pi * R *
          ‖rapidExponentialMomentFockEvaluation a ha (x : ℂ) f‖ ^ 2 := by rw [hid]
      _ ≤ E * C * I := hmean'
  have hcancelE : E * (q * R * A) ≤ E * (C * I) := by
    calc
      E * (q * R * A) = E * q * R * A := by ring
      _ ≤ Real.pi * R * K * A := hleft
      _ ≤ E * C * I := hright
      _ = E * (C * I) := by ring
  have hcancel : q * R * A ≤ C * I := le_of_mul_le_mul_left hcancelE hE
  change A ≤ rapidExponentialFockLocalEvaluationFactor a x * I
  rw [rapidExponentialFockLocalEvaluationFactor]
  change A ≤ C / (q * R) * I
  rw [show C / (q * R) * I = (C * I) / (q * R) by ring]
  exact (le_div_iff₀ hqR).2
    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hcancel)

end

end RHTower
