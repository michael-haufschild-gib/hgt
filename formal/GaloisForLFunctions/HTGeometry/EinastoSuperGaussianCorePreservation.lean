import GaloisForLFunctions.HTGeometry.EinastoSuperGaussianRegularGeometry

/-!
# Nontrivial metric changes with exactly preserved central curvature

The q>2 corrected-sign survivor is not a vanishing perturbation. Its actual
source is negative near the center; equation (15) therefore gives a strictly
negative correction there. Every positive coupling changes the metric while
preserving both central Ricci and Kretschmann limits. This separates local
metric determination from the two central curvature invariants.
-/
noncomputable section
open Filter Real Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- The corrected-sign source is nonzero near zero despite its zero central limit. -/
theorem einastoSuperGaussianSource_corrected_eventually_neg (d l k : ℝ) :
    ∀ᶠ t in atBot, einastoSuperGaussianSource d l k 1 (exp t) < 0 := by
  have hF := (einastoShapeSourceFactor_continuous d l (einastoSuperGaussianShape k)).continuousAt.tendsto.comp
    tendsto_exp_atBot
  have hN := hF.eventually (eventually_lt_nhds (einastoShapeSourceFactor_core_neg d l (einastoSuperGaussianShape k)))
  filter_upwards [hN] with t ht
  have hW : 0 < einastoSuperGaussianWeight l k (exp t) := by
    unfold einastoSuperGaussianWeight
    positivity
  simp only [einastoSuperGaussianSource, einastoShapeSourceDefect, sub_self, zero_mul, zero_div, add_zero]
  exact mul_neg_of_pos_of_neg hW ht

/-- The integral correction is strictly nonzero on a whole central neighborhood. -/
theorem einastoSuperGaussianCorrection_corrected_eventually_neg (d l k : ℝ) :
    ∀ᶠ t in atBot, einastoSuperGaussianCorrection d l k 1 (exp t) < 0 := by
  obtain ⟨T, hT⟩ := eventually_atBot.mp (einastoSuperGaussianSource_corrected_eventually_neg d l k)
  filter_upwards [eventually_le_atBot T] with t ht
  have hE (u : ℝ) (hu : 0 < u) (hut : u ≤ exp t) : einastoSuperGaussianSource d l k 1 u < 0 := by
    have hlu : log u ≤ t := by
      apply exp_le_exp.mp
      rw [exp_log hu]
      exact hut
    have h := hT (log u) (hlu.trans ht)
    simpa only [exp_log hu] using h
  have hc : Continuous (fun u : ℝ => -(8 * Real.pi * u ^ (2 : ℕ) * einastoSuperGaussianSource d l k 1 u)) :=
    ((continuous_const.mul (continuous_id.pow 2)).mul (einastoSuperGaussianSource_continuous d l k 1)).neg
  have hi : 0 < ∫ u in (0 : ℝ)..exp t, -(8 * Real.pi * u ^ (2 : ℕ) * einastoSuperGaussianSource d l k 1 u) := by
    apply intervalIntegral.integral_pos (exp_pos t) hc.continuousOn
    · intro u hu
      have hu0 : 0 < u := hu.1
      have hp : 0 < 8 * Real.pi * u ^ (2 : ℕ) := by positivity
      exact (neg_pos.mpr (mul_neg_of_pos_of_neg hp (hE u hu.1 hu.2))).le
    · refine ⟨exp t, ⟨(exp_pos t).le, le_rfl⟩, ?_⟩
      have hp : 0 < 8 * Real.pi * exp t ^ (2 : ℕ) := by positivity
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hp (hE (exp t) (exp_pos t) le_rfl))
  rw [intervalIntegral.integral_neg] at hi
  rw [einastoSuperGaussianCorrection_integral]
  exact div_neg_of_neg_of_pos (neg_pos.mp hi) (exp_pos t)

/-- Positive coupling strictly changes the metric arbitrarily close to its regular center. -/
theorem einastoSuperGaussian_corrected_metric_decreases (d l k b : ℝ) :
    ∀ᶠ t in atBot, einastoSuperGaussianPerturbedMetric d l k 1 (exp b) (exp t) <
      einastoMetric d l (einastoSuperGaussianShape k) (exp t) := by
  filter_upwards [einastoSuperGaussianCorrection_corrected_eventually_neg d l k] with t ht
  have hp := mul_neg_of_pos_of_neg (exp_pos b) ht
  unfold einastoSuperGaussianPerturbedMetric
  linarith

theorem einastoSuperGaussian_corrected_metric_nontrivial (d l k b : ℝ) :
    einastoSuperGaussianPerturbedMetric d l k 1 (exp b) ≠ einastoMetric d l (einastoSuperGaussianShape k) := by
  intro he
  obtain ⟨t, ht⟩ := (einastoSuperGaussian_corrected_metric_decreases d l k b).exists
  rw [he] at ht
  exact (lt_irrefl _ ht)

/-- Different actual metrics can have identical central Ricci and Kretschmann data. -/
theorem einastoSuperGaussian_nontrivial_core_preserver (d l k b : ℝ) :
    ∃ f : ℝ → ℝ, f ≠ einastoMetric d l (einastoSuperGaussianShape k) ∧ Continuous f ∧ f 0 = 1 ∧
      (∀ᶠ t in atBot, 0 < f (exp t)) ∧
      Tendsto (fun t => radialRicciScalar f (exp t)) atBot (𝓝 (-32 * Real.pi * exp d)) ∧
      Tendsto (fun t => radialKretschmannScalar f (exp t)) atBot (𝓝 (512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3)) := by
  exact ⟨einastoSuperGaussianPerturbedMetric d l k 1 (exp b),
    einastoSuperGaussian_corrected_metric_nontrivial d l k b,
    einastoSuperGaussianPerturbedMetric_continuous d l k 1 (exp b),
    einastoSuperGaussianPerturbedMetric_center d l k 1 (exp b),
    einastoSuperGaussianPerturbedMetric_eventually_pos d l k 1 (exp b),
    einastoSuperGaussian_corrected_Ricci_preserved d l k (exp b),
    einastoSuperGaussian_corrected_Kretschmann_preserved d l k (exp b)⟩

end GaloisForLFunctions.HTGeometry
