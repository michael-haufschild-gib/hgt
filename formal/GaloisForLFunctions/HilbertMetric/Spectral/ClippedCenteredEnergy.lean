import GaloisForLFunctions.HilbertMetric.Spectral.ClippedCongruence

/-!
# Centered interaction matrices

For an interaction matrix `S`, the unit-centered defect of `I + S` retains the
square energy of `S` up to the cutoff. Zero-diagonal interactions also satisfy
the mixed-multiplicity inequality, irrespective of their signs or inertia.
-/

open Matrix
open scoped NNReal
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem shifted_defect_lower {S : Matrix ι ι ℂ} (hS : S.IsHermitian) (τ : ℝ≥0) :
    min (trace (S * S)).re ((τ : ℝ) ^ 2) ≤ defectEnergy τ (1 + S) := by
  have h := defectEnergy_min_bound (Matrix.isHermitian_one.add hS) τ
  have hc : (trace ((1 + S) * (1 + S))).re - 2 * (trace (1 + S)).re + Fintype.card ι =
      (trace (S * S)).re := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.trace_add, Matrix.trace_one, Complex.add_re, Complex.natCast_re]
    ring
  rwa [hc] at h

/-- Every matrix entry supplies a clipped lower certificate for interaction energy. -/
theorem shifted_entry_lower {S : Matrix ι ι ℂ} (hS : S.IsHermitian)
    (τ : ℝ≥0) (i j : ι) :
    min (Complex.normSq (S i j)) ((τ : ℝ) ^ 2) ≤ defectEnergy τ (1 + S) := by
  have he : Complex.normSq (S i j) ≤ (trace (S * S)).re := by
    rw [trace_square hS]
    exact (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _)
        (Finset.mem_univ i))
  exact (min_le_min_right _ he).trans (shifted_defect_lower hS τ)

/-- Mixed weighting preserves any signed, zero-diagonal interaction defect. -/
theorem shifted_mixed_bound {S : Matrix ι ι ℂ} (hS : S.IsHermitian)
    (hdiag : ∀ i, S i i = 0) (doubled : ι → Bool) (τ : ℝ≥0) :
    min (trace (S * S)).re ((τ : ℝ) ^ 2) + ∑ i, binaryWeight doubled i ^ 2 ≤
      energy (mixedCutoff τ) (weightedGram (binaryWeight doubled) (1 + S)) := by
  have hm := binary_mixed_bound (Matrix.isHermitian_one.add hS)
    (fun i => by simp [Matrix.add_apply, hdiag i]) doubled τ
  exact (add_le_add (shifted_defect_lower hS τ) le_rfl).trans hm

end
end GaloisForLFunctions.HilbertMetric.Clipped
