/-
# Chen--Gupta--Li Class-I complex Abel deweighting

Finite summation by parts for a complex Dirichlet block and real weights.
This is the exact algebraic core required to remove the real
`n^{-Re rho} exp(-n/Y)` weights from the current literal Class-I witness.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassIHeterogeneousPacket

open Complex

noncomputable section

namespace RHTower

/-- Prefix sum of a complex coefficient sequence. -/
def cglComplexPartialSum (a : ℕ → ℂ) (K : ℕ) : ℂ :=
  ∑ j ∈ Finset.range K, a j

/-- Exact finite Abel summation for a complex sequence against real weights. -/
theorem cglComplexAbelSummation (a : ℕ → ℂ) (w : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, a j * (w j : ℂ)) =
      (w (N - 1) : ℂ) * cglComplexPartialSum a N -
        ∑ j ∈ Finset.range (N - 1), ((w (j + 1) - w j : ℝ) : ℂ) *
          cglComplexPartialSum a (j + 1) := by
  have hbp := Finset.sum_range_by_parts (fun j : ℕ => (w j : ℂ)) a N
  have hleft : (∑ j ∈ Finset.range N, a j * (w j : ℂ)) =
      ∑ j ∈ Finset.range N, (w j : ℂ) * a j := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hleft]
  simpa [smul_eq_mul, cglComplexPartialSum] using hbp

/-- Norm envelope following from finite complex Abel summation. -/
theorem norm_cglComplexAbelSummation_le (a : ℕ → ℂ) (w : ℕ → ℝ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, a j * (w j : ℂ)‖ ≤
      |w (N - 1)| * ‖cglComplexPartialSum a N‖ +
        ∑ j ∈ Finset.range (N - 1), |w (j + 1) - w j| *
          ‖cglComplexPartialSum a (j + 1)‖ := by
  rw [cglComplexAbelSummation]
  calc
    ‖(w (N - 1) : ℂ) * cglComplexPartialSum a N -
        ∑ j ∈ Finset.range (N - 1), ((w (j + 1) - w j : ℝ) : ℂ) *
          cglComplexPartialSum a (j + 1)‖ ≤
      ‖(w (N - 1) : ℂ) * cglComplexPartialSum a N‖ +
        ‖∑ j ∈ Finset.range (N - 1), ((w (j + 1) - w j : ℝ) : ℂ) *
          cglComplexPartialSum a (j + 1)‖ := norm_sub_le _ _
    _ ≤ ‖(w (N - 1) : ℂ) * cglComplexPartialSum a N‖ +
        ∑ j ∈ Finset.range (N - 1),
          ‖((w (j + 1) - w j : ℝ) : ℂ) * cglComplexPartialSum a (j + 1)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ = _ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]

end RHTower
