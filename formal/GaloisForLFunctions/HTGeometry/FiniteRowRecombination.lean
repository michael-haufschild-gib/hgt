import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Recombination with coefficients depending on the observation

The finite form of Lemma B.3 of *The Quasi-Riemann Hypothesis* controls a
recombined family by a common coefficient envelope. Taking that envelope
to be the norm on a finite function space removes any separate domination
assumption. The observation weights are nonnegative real numbers.
-/

noncomputable section
open scoped BigOperators NNReal

namespace GaloisForLFunctions.HTGeometry

variable {ι ρ 𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- Arbitrary coefficient mass replaces the unit-mass normalization in Jensen's bound. -/
theorem norm_sum_smul_sq_le_mass (s : Finset ι) (c : ι → 𝕜) (v : ι → E) :
    ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤
      (∑ i ∈ s, ‖c i‖) * ∑ i ∈ s, ‖c i‖ * ‖v i‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (f := fun i => ‖c i‖) (g := fun i => ‖c i‖ * ‖v i‖ ^ 2) s
  · intro i _
    exact norm_nonneg _
  · intro i _
    positivity
  · intro i _
    rw [norm_smul, mul_pow]
    exact le_of_eq (by ring)

/-- A common envelope controls one row even when every coefficient depends on that row. -/
theorem norm_sum_smul_sq_le_row_envelope [Fintype ρ]
    (s : Finset ι) (c : ι → ρ → 𝕜) (v : ι → ρ → E) (r : ρ) :
    ‖∑ i ∈ s, c i r • v i r‖ ^ 2 ≤
      (∑ i ∈ s, ‖c i‖) * ∑ i ∈ s, ‖c i‖ * ‖v i r‖ ^ 2 := by
  refine (norm_sum_smul_sq_le_mass s (fun i => c i r) (fun i => v i r)).trans ?_
  apply mul_le_mul
  · exact Finset.sum_le_sum fun i _ => norm_le_pi_norm (c i) r
  · exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (norm_le_pi_norm (c i) r) (sq_nonneg _)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  · exact Finset.sum_nonneg fun i _ => norm_nonneg _

/-- Finite weighted mean-square recombination with its canonical row envelope. -/
theorem sum_weight_norm_sum_smul_sq_le_row_envelope [Fintype ρ]
    (s : Finset ι) (w : ρ → ℝ≥0) (c : ι → ρ → 𝕜) (v : ι → ρ → E) :
    (∑ r, (w r : ℝ) * ‖∑ i ∈ s, c i r • v i r‖ ^ 2) ≤
      (∑ i ∈ s, ‖c i‖) *
        ∑ i ∈ s, ‖c i‖ * ∑ r, (w r : ℝ) * ‖v i r‖ ^ 2 := by
  calc
    _ ≤ ∑ r, (w r : ℝ) *
        ((∑ i ∈ s, ‖c i‖) * ∑ i ∈ s, ‖c i‖ * ‖v i r‖ ^ 2) :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
        (norm_sum_smul_sq_le_row_envelope s c v r) (w r).coe_nonneg
    _ = _ := by
      simp_rw [mul_left_comm (w _ : ℝ), ← Finset.mul_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- Recombination with a common coefficient sequence, with no normalization premise. -/
theorem sum_weight_norm_sum_smul_sq_le_mass [Fintype ρ]
    (s : Finset ι) (w : ρ → ℝ≥0) (c : ι → 𝕜) (v : ι → ρ → E) :
    (∑ r, (w r : ℝ) * ‖∑ i ∈ s, c i • v i r‖ ^ 2) ≤
      (∑ i ∈ s, ‖c i‖) *
        ∑ i ∈ s, ‖c i‖ * ∑ r, (w r : ℝ) * ‖v i r‖ ^ 2 := by
  calc
    _ ≤ ∑ r, (w r : ℝ) *
        ((∑ i ∈ s, ‖c i‖) * ∑ i ∈ s, ‖c i‖ * ‖v i r‖ ^ 2) :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
        (norm_sum_smul_sq_le_mass s c (fun i => v i r)) (w r).coe_nonneg
    _ = _ := by
      simp_rw [mul_left_comm (w _ : ℝ), ← Finset.mul_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      ring

end GaloisForLFunctions.HTGeometry
