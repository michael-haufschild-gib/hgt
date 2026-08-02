import GaloisForLFunctions.RHTower.BurnolSoninContinuousEvaluation

/-!
# The aperture bound in its Riesz-vector form

The completed Mellin evaluation vector of Burnol's extended Sonine space carries the aperture
estimate directly in its norm.  Fréchet--Riesz is an isometry, so the operator bound of the
evaluation functional transfers verbatim to the evaluation vector:

`‖k_{w,a}‖ ≤ C(w) a^(-|Re w - 1/2|)`,

with `C(w) = ‖π^(-w/2) Γ(w/2)‖ (1/‖1-w‖ + 1/sqrt (2 Re w - 1)) / sqrt 2` the explicit head/tail
constant.  This is the boxed ambient off-axis bound in the form in which it is used: a statement
about the evaluation vector, not about the functional.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

theorem soninApertureConstant_nonneg (w : ℂ) : 0 ≤ soninApertureConstant w := by
  rw [soninApertureConstant]
  have h1 : (0 : ℝ) ≤ 1 / ‖1 - w‖ := by positivity
  have h2 : (0 : ℝ) ≤ 1 / Real.sqrt (2 * w.re - 1) := by positivity
  have := norm_nonneg (mellinCompletionFactor w)
  nlinarith

theorem burnolExtendedSoninEvaluationBound_nonneg (w : ℂ)
    {a : ℝ} (ha : 0 < a) : 0 ≤ burnolExtendedSoninEvaluationBound w a := by
  rw [burnolExtendedSoninEvaluationBound]
  have h1 := soninApertureConstant_nonneg w
  have h2 : (0 : ℝ) < a ^ (1 / 2 - w.re) := Real.rpow_pos_of_pos ha _
  positivity

/-- **Aperture bound for the evaluation vector.**  Testing the completed Mellin functional on its
own Riesz vector turns the operator estimate into a bound on the vector norm. -/
theorem norm_burnolExtendedSoninEvaluationVector_le
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a : ℝ} (ha : 0 < a) :
    ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ≤
      burnolExtendedSoninEvaluationBound w a := by
  letI : Fact (0 < a) := ⟨ha⟩
  set k := burnolExtendedSoninEvaluationVector w a hlo hhi ha with hk
  set B := burnolExtendedSoninEvaluationBound w a with hB
  have hBnn : 0 ≤ B := burnolExtendedSoninEvaluationBound_nonneg w ha
  have hself : ‖(inner ℂ k k : ℂ)‖ = ‖k‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg k)]
  have heval := inner_burnolExtendedSoninEvaluationVector w a hlo hhi ha k
  have hbound := norm_burnolExtendedSoninEvaluationLinearMap_le hlo hhi ha k
  have hsq : ‖k‖ ^ 2 ≤ B * ‖k‖ := by
    rw [← hself, heval]
    exact hbound
  rcases eq_or_lt_of_le (norm_nonneg k) with h0 | h0
  · rw [← h0]
    exact hBnn
  · have hmul : ‖k‖ * ‖k‖ ≤ B * ‖k‖ := by
      rw [← pow_two]
      exact hsq
    exact le_of_mul_le_mul_right (by linarith [hmul]) h0

/-- **The boxed ambient off-axis bound.**  Above the critical line the evaluation vector has
aperture exponent exactly the horizontal displacement `|Re w - 1/2|`. -/
theorem norm_burnolExtendedSoninEvaluationVector_le_aperture
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a : ℝ} (ha : 0 < a) :
    ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ≤
      soninApertureConstant w / Real.sqrt 2 * a ^ (-|w.re - 1 / 2|) := by
  have h := norm_burnolExtendedSoninEvaluationVector_le hlo hhi ha
  have habs : -|w.re - 1 / 2| = 1 / 2 - w.re := by
    rw [abs_of_pos (by linarith)]
    ring
  rw [habs]
  rw [burnolExtendedSoninEvaluationBound] at h
  calc ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖
      ≤ soninApertureConstant w * a ^ (1 / 2 - w.re) / Real.sqrt 2 := h
    _ = soninApertureConstant w / Real.sqrt 2 * a ^ (1 / 2 - w.re) := by ring

end RHTower
