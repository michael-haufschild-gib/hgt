import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCesaroCriterion

/-!
# Exact weighted form of the convolution-half Cesàro source

The Cesàro average is exactly a first-order triangular/Riesz mean of the literal
`squarefreeConvolutionHalf` Dirichlet coefficients.  This finite identity exposes the arithmetic
quantity that must be estimated for any slow scheduled continuation.
-/

open Complex Filter Metric Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem sum_range_partial_sums_eq_triangular (a : ℕ → ℂ) :
    ∀ N : ℕ,
      ∑ M ∈ Finset.range N, (∑ n ∈ Finset.range M, a n) =
        ∑ n ∈ Finset.range N, ((N - (n + 1) : ℕ) : ℂ) * a n := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_range] at hn
      have hweight : N + 1 - (n + 1) = (N - (n + 1)) + 1 := by omega
      rw [hweight]
      push_cast
      ring

/-- Numerator form of the exact triangular/Riesz kernel underlying Cesàro averaging. -/
theorem sum_squarefreeHalfDirichletPartialSum_eq_triangular
    (N : ℕ) (s : ℂ) :
    ∑ M ∈ Finset.range N, squarefreeHalfDirichletPartialSum M s =
      ∑ n ∈ Finset.range N, ((N - (n + 1) : ℕ) : ℂ) *
        LSeries.term squarefreeConvolutionHalf s n := by
  exact sum_range_partial_sums_eq_triangular
    (fun n => LSeries.term squarefreeConvolutionHalf s n) N

/-- Exact triangular/Riesz weight formula for the canonical Cesàro half-source. -/
theorem squarefreeHalfCesaroSum_eq_triangular (N : ℕ) (s : ℂ) :
    squarefreeHalfCesaroSum N s =
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, ((N - (n + 1) : ℕ) : ℂ) *
        LSeries.term squarefreeConvolutionHalf s n := by
  rw [squarefreeHalfCesaroSum, sum_squarefreeHalfDirichletPartialSum_eq_triangular]

end

end RHTower
