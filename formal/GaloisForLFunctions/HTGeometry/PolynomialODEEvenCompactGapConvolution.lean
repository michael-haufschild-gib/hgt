import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapDet
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSourceCoefficients

namespace HTGeometry
noncomputable section

/-- Finite gap-coordinate convolution, with a literal range of indices. -/
theorem evenCompactGapCoeff_mul (p q : Polynomial ℝ) (n : ℕ) :
    (p*q).coeff n = ∑ k ∈ Finset.range (n+1), p.coeff k*q.coeff (n-k) := by
  rw [Polynomial.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i*q.coeff j) n

/-- Squared source entries use the same finite convolution. -/
theorem evenCompactGapCoeff_sq (p : Polynomial ℝ) (n : ℕ) :
    (p^2).coeff n = ∑ k ∈ Finset.range (n+1), p.coeff k*p.coeff (n-k) := by
  rw [pow_two, evenCompactGapCoeff_mul]

/-- Cubed source entries retain the square and the final source factor. -/
theorem evenCompactGapCoeff_cube (p : Polynomial ℝ) (n : ℕ) :
    (p^3).coeff n = ∑ k ∈ Finset.range (n+1), (p^2).coeff k*p.coeff (n-k) := by
  rw [pow_succ, evenCompactGapCoeff_mul]

end
end HTGeometry
