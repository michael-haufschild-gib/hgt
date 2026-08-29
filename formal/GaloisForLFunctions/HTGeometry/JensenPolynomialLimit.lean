import GaloisForLFunctions.HTGeometry.JensenPolynomialSplits
import GaloisForLFunctions.HTGeometry.RealRootedCoefficientLimit

/-!
# Jensen polynomials of a coefficientwise limit of real-rooted polynomials

A coefficient sequence that is the coefficientwise limit of real-rooted real polynomials has
real-rooted Jensen polynomials at every degree.  The Jensen polynomial is a fixed finite linear
combination of the coefficients, so it is itself such a limit, and real-rootedness is closed under
coefficientwise limits of bounded degree.
-/

open Polynomial Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem coeff_jensenPoly (c : ℕ → ℝ) (d i : ℕ) :
    (jensenPoly c d).coeff i = if i ≤ d then c i * (d.descFactorial i : ℝ) else 0 := by
  classical
  have key : ∀ b : ℕ, (C (c b * (d.descFactorial b : ℝ)) * X ^ b : ℝ[X]).coeff i
      = if i = b then c b * (d.descFactorial b : ℝ) else 0 := by
    intro b
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : i = b <;> simp [h]
  rw [jensenPoly, Polynomial.finsetSum_coeff]
  simp only [key]
  rw [Finset.sum_ite_eq]
  by_cases h : i ≤ d
  · rw [if_pos (Finset.mem_range.2 (by omega)), if_pos h]
  · rw [if_neg (fun hmem => h (Nat.lt_succ_iff.1 (Finset.mem_range.1 hmem))), if_neg h]

theorem natDegree_jensenPoly_le (c : ℕ → ℝ) (d : ℕ) : (jensenPoly c d).natDegree ≤ d := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun i hi => ?_
  rw [coeff_jensenPoly, if_neg (by omega)]

/-- **Jensen polynomials of a coefficientwise limit of real-rooted polynomials are real-rooted.** -/
theorem splits_jensenPoly_of_tendsto_coeff {c : ℕ → ℝ} {p : ℕ → ℝ[X]}
    (hsplit : ∀ m, (p m).Splits)
    (hlim : ∀ j, Tendsto (fun m => (p m).coeff j) atTop (𝓝 (c j))) (d : ℕ) :
    (jensenPoly c d).Splits := by
  classical
  by_cases hzero : jensenPoly c d = 0
  · rw [hzero]
    exact Polynomial.Splits.of_natDegree_le_one (by simp)
  refine splits_of_tendsto_coeff (d := d) (qs := fun m => jensenPoly (fun i => (p m).coeff i) d)
    (fun m => natDegree_jensenPoly_le _ _) (natDegree_jensenPoly_le _ _)
    (fun m => splits_jensenPoly_of_splits (hsplit m) d) (fun j => ?_) hzero
  simp only [coeff_jensenPoly]
  by_cases hj : j ≤ d
  · simp only [if_pos hj]
    exact (hlim j).mul_const _
  · simp only [if_neg hj]
    exact tendsto_const_nhds

end

end GaloisForLFunctions.HTGeometry
