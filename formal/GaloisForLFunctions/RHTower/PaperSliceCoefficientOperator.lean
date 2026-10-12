import GaloisForLFunctions.RHTower.PaperSliceCoefficientSource
import GaloisForLFunctions.RHTower.SuzukiDiagonalResolventInstantiation
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace

/-! # A compact operator carrying every signed slice coefficient

The diagonal is the literal Taylor source. Its positivity is exactly the native
coefficient sign test; its compact-ideal cost vanishes unconditionally.
-/

noncomputable section

open Filter
open scoped Topology ENNReal

namespace RHTower.PaperSliceCoefficient

open GaloisForLFunctions.HTGeometry

theorem norm_coefficient_cast_le (t : ℝ) (n : ℕ) :
    ‖(coefficient t n : ℂ)‖ ≤ budget t := by
  rw [coefficient_cast]
  exact norm_source_le_budget t n

/-- Every original coefficient acts on its own unchanged Taylor coordinate. -/
def operator (t : ℝ) : EllTwo →L[ℂ] EllTwo :=
  diagonalOperator (fun n => (coefficient t n : ℂ)) (norm_coefficient_cast_le t)

theorem operator_apply (t : ℝ) (f : EllTwo) (n : ℕ) :
    operator t f n = (coefficient t n : ℂ) * f n := rfl

theorem operator_apply_source (t : ℝ) (f : EllTwo) (n : ℕ) :
    operator t f n = xiSliceCoeff t n * f n := by rw [operator_apply, coefficient_cast]

theorem operator_single (t : ℝ) (n : ℕ) :
    operator t (lp.single 2 n (1 : ℂ)) = lp.single 2 n (xiSliceCoeff t n) := by
  rw [operator, diagonalOperator_single, coefficient_cast]

theorem norm_operator_le (t : ℝ) : ‖operator t‖ ≤ budget t :=
  norm_diagonalOperator_le _ _

theorem selfAdjoint_operator (t : ℝ) : IsSelfAdjoint (operator t) :=
  GaloisForLFunctions.RHTower.isSelfAdjoint_diagonalOperator_ofReal _ _

def quadratic (t : ℝ) (f : EllTwo) : ℝ := (inner ℂ (operator t f) f).re

theorem quadratic_eq_tsum (t : ℝ) (f : EllTwo) :
    quadratic t f = ∑' n, coefficient t n * Complex.normSq (f n) := by
  rw [quadratic, lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner (operator t f) f)]
  apply tsum_congr
  intro n
  have hval : inner ℂ (operator t f n) (f n) =
      (coefficient t n : ℂ) * (Complex.normSq (f n) : ℂ) := by
    simp only [operator_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    rw [← Complex.mul_conj]
    ring
  rw [hval]
  simp

theorem quadratic_single (t : ℝ) (n : ℕ) :
    quadratic t (lp.single 2 n (1 : ℂ)) = coefficient t n := by
  rw [quadratic, lp.inner_single_right, operator_apply]
  simp [lp.single_apply, RCLike.inner_apply]

theorem positive_operator_iff (t : ℝ) :
    (operator t).IsPositive ↔ ∀ n, 0 ≤ coefficient t n := by
  constructor
  · intro h n
    have hn := h.re_inner_nonneg_left (lp.single 2 n (1 : ℂ))
    change 0 ≤ quadratic t (lp.single 2 n (1 : ℂ)) at hn
    rwa [quadratic_single] at hn
  · exact GaloisForLFunctions.RHTower.isPositive_diagonalOperator_ofReal _ _

theorem all_operator_positive_iff :
    (∀ t : Height, (operator t).IsPositive) ↔ RiemannHypothesis := by
  simp only [positive_operator_iff, ← negativeCount_zero_iff, all_negativeCount_zero_iff]

theorem compact_operator (t : ℝ) : IsCompactOperator (operator t) := by
  apply GaloisForLFunctions.RHTower.isCompactOperator_diagonalOperator
  simpa only [coefficient_cast, norm_zero] using (tendsto_source_zero t).norm

/-- The proven compact-ideal weight sees zero cost at every height, irrespective of sign. -/
theorem ideal_cost_zero (t : ℝ) : compactOperatorTraceCost EllTwo (operator t) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).2 (compact_operator t)

theorem ideal_cost_compact_correction (t : ℝ) (K : compactOperatorStarAlgebra EllTwo) :
    compactOperatorTraceCost EllTwo (operator t + K.val) = 0 := by
  rw [compactOperatorTraceCost_add_compact, ideal_cost_zero]

end RHTower.PaperSliceCoefficient
