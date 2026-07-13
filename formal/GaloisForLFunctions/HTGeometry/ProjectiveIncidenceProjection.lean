import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartGlobalIncidenceDimension
import GaloisForLFunctions.HTGeometry.EvaluationRankDefectTopology

/-!
# The evaluation rank defect is the projective incidence projection

The Krull-dimension calculation is performed on affine charts of the projectivized null-vector
incidence.  The topological Baire argument, however, uses the literal rectangular rank-defect
locus in packet space.  This file proves that these are exactly the same set.

This is the project-specific identification needed before the classical proper-projection and
Whitney-stratification theorems can be applied.  In particular, the identification is not hidden
inside the classical theorem interface.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped BigOperators

noncomputable section

/-- The expanded evaluation matrix-vector product, grouped first by monomial label and then by
coefficient degree. -/
theorem expandedDifferentialEvaluationMatrix_mulVec
    {row κ : Type} [Fintype row] [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (y : row × Fin n → ℂ) (c : κ × Fin (q + 1) → ℂ) (b : row) :
    (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec c b =
      ∑ a, (∑ d, c (a, d) * z b ^ (d : ℕ)) *
        (exponent a).prod (fun k e => y (b, k) ^ e) := by
  classical
  rw [Matrix.mulVec, dotProduct, ← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [expandedDifferentialEvaluationMatrix_apply]
  ring

/-- Packet points lying under some affine chart of the projectivized null-vector incidence.  The
existential union over `j` is the finite standard projective cover. -/
def projectiveChartIncidenceProjection
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) :
    Set (row × Fin n → ℂ) :=
  {y | ∃ j : κ × Fin (q + 1), ∃ x : projectiveChartVar j → ℂ,
    IsProjectiveChartIncidencePoint q n z j exponent x y}

/-- The literal rectangular rank defect is exactly the projection of the projectivized
null-vector incidence. -/
theorem expandedDifferentialEvaluationRankDefect_eq_projectiveChartIncidenceProjection
    {row κ : Type} [Fintype row] [Fintype κ]
    [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) :
    expandedDifferentialEvaluationRankDefect q n z exponent =
      projectiveChartIncidenceProjection q n z exponent := by
  classical
  ext y
  rw [mem_expandedDifferentialEvaluationRankDefect_iff]
  constructor
  · intro hnoninjective
    obtain ⟨c, d, hcd, hcne⟩ := Function.not_injective_iff.mp hnoninjective
    let v : κ × Fin (q + 1) → ℂ := c - d
    have hvne : v ≠ 0 := by
      intro hv
      apply hcne
      exact sub_eq_zero.mp (by simpa [v] using hv)
    have hvzero :
        (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec v = 0 := by
      rw [show v = c - d by rfl, Matrix.mulVec_sub, hcd, sub_self]
    obtain ⟨j, x, scale, hscale, hreconstruct⟩ :=
      exists_projectiveChart_reconstruction v hvne
    refine ⟨j, x, ?_⟩
    rw [isProjectiveChartIncidencePoint_iff]
    intro b
    have hb := congrFun hvzero b
    rw [Pi.zero_apply, expandedDifferentialEvaluationMatrix_mulVec] at hb
    have hscaled : scale *
          (∑ a, (∑ d, projectiveChartHomogenize j x (a, d) * z b ^ (d : ℕ)) *
            (exponent a).prod (fun k e => y (b, k) ^ e)) = 0 := by
      calc
        scale *
            (∑ a, (∑ d, projectiveChartHomogenize j x (a, d) * z b ^ (d : ℕ)) *
              (exponent a).prod (fun k e => y (b, k) ^ e)) =
          ∑ a, (∑ d, v (a, d) * z b ^ (d : ℕ)) *
            (exponent a).prod (fun k e => y (b, k) ^ e) := by
          simp_rw [hreconstruct, Finset.mul_sum, Finset.sum_mul]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ = 0 := hb
    exact (mul_eq_zero.mp hscaled).resolve_left hscale
  · rintro ⟨j, x, hincidence⟩ hinjective
    let c : κ × Fin (q + 1) → ℂ := projectiveChartHomogenize j x
    have hcne : c ≠ 0 := by
      intro hc
      have hj := congrFun hc j
      simp [c] at hj
    have hczero :
        (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec c = 0 := by
      funext b
      rw [Pi.zero_apply, expandedDifferentialEvaluationMatrix_mulVec]
      exact (isProjectiveChartIncidencePoint_iff q n z j exponent x y).mp hincidence b
    have hc0 : c = 0 := hinjective (by simpa using hczero)
    exact hcne hc0

end

end GaloisForLFunctions.HTGeometry
