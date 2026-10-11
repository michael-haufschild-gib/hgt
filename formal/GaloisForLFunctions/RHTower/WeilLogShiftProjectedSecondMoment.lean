import GaloisForLFunctions.RHTower.WeilLogShiftProjectedWeakLimit
import GaloisForLFunctions.RHTower.WeilLogShiftFluctuationRankOneLimit
import Mathlib.MeasureTheory.Function.L2Space

/-! Every projected finite law has convergent second moment, including zero-variance projections. -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalProjectedProbabilityLaw_integrable (r k : ℕ) (a b : ℝ) (f : ℝ → ℝ) :
    Integrable f (finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ) :=
  finiteWeilCanonicalObservableLaw_integrable r k _ f

theorem finiteWeilProjectedGaussian_integrable_sq (a b : ℝ) :
    Integrable (fun x : ℝ => x ^ 2) (finiteWeilProjectedGaussian a b : Measure ℝ) := by
  exact (memLp_id_gaussianReal (μ := 0)
    (v := NNReal.mk ((a + b) ^ 2 / 4) (by positivity)) 2).integrable_sq

theorem finiteWeilProjectedGaussian_second_moment (a b : ℝ) :
    (∫ x, x ^ 2 ∂(finiteWeilProjectedGaussian a b : Measure ℝ)) = (a + b) ^ 2 / 4 := by
  change (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 (NNReal.mk ((a + b) ^ 2 / 4) (by positivity)))) =
    (a + b) ^ 2 / 4
  have h := variance_fun_id_gaussianReal (μ := 0)
    (v := NNReal.mk ((a + b) ^ 2 / 4) (by positivity))
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable,
    integral_id_gaussianReal] at h
  simpa only [sub_zero, NNReal.coe_mk] using h

theorem finiteWeilCanonicalProjectedProbabilityLaw_second_moment (r k : ℕ) (a b : ℝ) :
    (∫ x, x ^ 2 ∂(finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ)) =
      a ^ 2 * (finiteWeilCanonicalEdgeIndexVariance r k / ((r + 1 : ℕ) : ℝ)) +
        (2 * a * b) * finiteWeilCanonicalIndexCorrectionCovariance r k +
        b ^ 2 * (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionVariance r k) := by
  rw [finiteWeilCanonicalProjectedProbabilityLaw, finiteWeilCanonicalObservableLaw_integral_real]
  unfold finiteWeilCanonicalEdgeIndexVariance finiteWeilCanonicalEdgeLogCorrectionVariance
    finiteWeilCanonicalIndexCorrectionCovariance
  simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_pow, Real.sq_sqrt (by positivity)]
  have hn : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  ring_nf

theorem tendsto_finiteWeilCanonicalProjectedProbabilityLaw_second_moment
    (t : ℕ → ℕ) (a b : ℝ) :
    Tendsto (fun r => ∫ x, x ^ 2 ∂(finiteWeilCanonicalProjectedProbabilityLaw r
      (2 * (r + 1) ^ 2 + t r) a b : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ 2 ∂(finiteWeilProjectedGaussian a b : Measure ℝ))) := by
  simp_rw [finiteWeilCanonicalProjectedProbabilityLaw_second_moment]
  rw [finiteWeilProjectedGaussian_second_moment]
  have h := (((tendsto_finiteWeilCanonicalEdgeIndexVariance_quarter t).const_mul (a ^ 2)).add
    ((tendsto_finiteWeilCanonicalIndexCorrectionCovariance_quarter t).const_mul (2 * a * b))).add
      ((tendsto_finiteWeilCanonicalEdgeLogCorrectionVariance_quarter t).const_mul (b ^ 2))
  convert h using 1
  ring_nf

end RHTower
