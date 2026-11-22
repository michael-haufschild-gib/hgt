import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.ValueField

/-! # A single real equation for polynomial specialization to zero -/
open Polynomial
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
variable {A : Type*} [CommRing A]

/-- Sum of the squared coefficients. Its specialized real value detects
whether the entire polynomial specializes to zero. -/
def coefficientSquares (p : A[X]) : A := ∑ n ∈ p.support, (p.coeff n)^2

theorem coefficientSquares_zero_iff (φ : A →+* ℝ) (p : A[X]) :
    φ (coefficientSquares p) = 0 ↔ p.map φ = 0 := by
  classical
  rw [coefficientSquares, map_sum]
  simp only [map_pow]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  constructor
  · intro h
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hn : n ∈ p.support
    · exact pow_eq_zero (h n hn)
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
  · intro h n _
    have hv := congrArg (fun P : ℝ[X] => P.coeff n) h
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hv
    rw [hv, zero_pow (by decide : 2 ≠ 0)]

/-- Two equations can be combined without changing their real zero set. -/
theorem pair_squares_zero (φ : A →+* ℝ) (a b : A) :
    φ (a^2 + b^2) = 0 ↔ φ a = 0 ∧ φ b = 0 := by
  rw [map_add,map_pow,map_pow,add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)]
  simp

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
