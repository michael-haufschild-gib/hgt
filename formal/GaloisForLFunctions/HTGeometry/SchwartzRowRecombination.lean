import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
Continuous row recombination with the common pointwise envelope of a finite
Schwartz family. Bounded continuous responses make every required integral
convergent automatically. The estimate keeps the family energy inside the
integral, as required when the smoothing weight depends on the row.
This is the continuous recombination mechanism of paper2, Appendix B.3,
with a canonical envelope and fully discharged integrability conditions.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction NNReal

variable {ρ E : Type*} [Fintype ρ] [NormedAddCommGroup E] [NormedSpace ℂ E]

def schwartzRowEnvelope (c : ρ → SchwartzMap ℝ ℂ) (u : ℝ) : ℝ :=
  ‖fun r => c r u‖

theorem continuous_schwartzRowEnvelope (c : ρ → SchwartzMap ℝ ℂ) :
    Continuous (schwartzRowEnvelope c) :=
  (continuous_pi fun r => (c r).continuous).norm

theorem norm_le_schwartzRowEnvelope (c : ρ → SchwartzMap ℝ ℂ) (r : ρ) (u : ℝ) :
    ‖c r u‖ ≤ schwartzRowEnvelope c u := norm_le_pi_norm (fun r => c r u) r

theorem integrable_schwartzRowEnvelope (c : ρ → SchwartzMap ℝ ℂ) :
    Integrable (schwartzRowEnvelope c) := by
  have hsum : Integrable (fun u : ℝ => ∑ r, ‖c r u‖) :=
    integrable_finsetSum Finset.univ (fun r _ => (c r).integrable.norm)
  refine hsum.mono' (continuous_schwartzRowEnvelope c).aestronglyMeasurable ?_
  filter_upwards with u
  change ‖‖fun r => c r u‖‖ ≤ _
  rw [norm_norm]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun r _ => norm_nonneg _)).2
  intro r
  exact Finset.single_le_sum (fun i _ => norm_nonneg (c i u)) (Finset.mem_univ r)

omit [NormedSpace ℂ E] in
private theorem integrable_envelope_norm_pow
    (c : ρ → SchwartzMap ℝ ℂ) (v : ℝ →ᵇ E) (k : ℕ) :
    Integrable (fun u : ℝ => schwartzRowEnvelope c u * ‖v u‖ ^ k) := by
  apply (integrable_schwartzRowEnvelope c).mul_bdd (c := ‖v‖ ^ k)
    (v.continuous.norm.pow k).aestronglyMeasurable
  filter_upwards with u
  change ‖‖v u‖ ^ k‖ ≤ ‖v‖ ^ k
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (v.norm_coe_le_norm u) k

theorem integrable_schwartz_smul_bounded (c : SchwartzMap ℝ ℂ) (v : ℝ →ᵇ E) :
    Integrable (fun u : ℝ => c u • v u) :=
  c.integrable.smul_bdd ‖v‖ v.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall v.norm_coe_le_norm)

/-- A row's integral is controlled by the common envelope mass and its own energy. -/
theorem norm_integral_schwartz_smul_sq_le_row_envelope
    (c : ρ → SchwartzMap ℝ ℂ) (v : ℝ →ᵇ E) (r : ρ) :
    ‖∫ u : ℝ, c r u • v u‖ ^ 2 ≤
      (∫ u : ℝ, schwartzRowEnvelope c u) *
        ∫ u : ℝ, schwartzRowEnvelope c u * ‖v u‖ ^ 2 := by
  have hnorm : ‖∫ u : ℝ, c r u • v u‖ ≤
      ∫ u : ℝ, schwartzRowEnvelope c u * ‖v u‖ := by
    apply norm_integral_le_of_norm_le
      (by simpa using integrable_envelope_norm_pow c v 1)
    filter_upwards with u
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_le_schwartzRowEnvelope c r u) (norm_nonneg _)
  have hcs := sq_integral_weighted_le
    (fun u => norm_nonneg (fun r => c r u))
    (continuous_schwartzRowEnvelope c).aestronglyMeasurable
    v.continuous.norm.aestronglyMeasurable
    (integrable_schwartzRowEnvelope c) (integrable_envelope_norm_pow c v 2)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs

/-- Continuous counterpart of finite row recombination; no integrability premises remain. -/
theorem sum_weight_norm_integral_schwartz_smul_sq_le_row_envelope
    (c : ρ → SchwartzMap ℝ ℂ) (v : ρ → ℝ →ᵇ E) (w : ρ → ℝ≥0) :
    (∑ r, (w r : ℝ) * ‖∫ u : ℝ, c r u • v r u‖ ^ 2) ≤
      (∫ u : ℝ, schwartzRowEnvelope c u) *
        ∫ u : ℝ, schwartzRowEnvelope c u * ∑ r, (w r : ℝ) * ‖v r u‖ ^ 2 := by
  calc
    _ ≤ ∑ r, (w r : ℝ) * ((∫ u : ℝ, schwartzRowEnvelope c u) *
        ∫ u : ℝ, schwartzRowEnvelope c u * ‖v r u‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (norm_integral_schwartz_smul_sq_le_row_envelope c (v r) r) (w r).coe_nonneg
    _ = _ := by
      simp_rw [Finset.mul_sum]
      simp_rw [mul_left_comm (schwartzRowEnvelope c _) (w _ : ℝ)]
      rw [integral_finsetSum Finset.univ (fun r _ =>
        (integrable_envelope_norm_pow c (v r) 2).const_mul (w r))]
      simp_rw [integral_const_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

end GaloisForLFunctions.HTGeometry
